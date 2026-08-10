# Supported and unsupported behavior

This document is the authoritative feature boundary for the current pre-release
implementation. A construct not listed as supported should be assumed
unsupported until a generation or runtime test establishes otherwise.

## PostgreSQL versions

- PostgreSQL 18 is the default canonical generation server (currently pinned
  at 18.2).
- PostgreSQL 17 can also be selected as the canonical generator and is pinned
  at 17.8.
- Generated attachment accepts only majors listed in both the manifest and the
  `lean_pg_library.server_majors` attribute.
- Probe adapters and namespaced tool repositories exist only for majors 17 and
  18.

The compatibility test compares normalized, major-independent schema and query
semantics. Passing it does not assert that arbitrary application SQL behaves
identically across majors.

## Host platforms

The Bazel generation and live-test lifecycle currently supports Linux and
macOS POSIX hosts with Nix, Bash, Unix-domain sockets, and directory runfiles.
Windows and manifest-only Bazel runfiles (`--enable_runfiles=false`) are not
supported. CI exercises Linux; macOS compatibility is maintained by the build
configuration but should be treated as supported only while its live tests
remain green.

## Schema and query discovery

Supported:

- ordered DDL replay into an empty database;
- explicitly named schemas;
- enums, domains, array types, named composites, ranges, and multiranges;
- tables, partitioned tables, views, materialized views, and foreign-table
  descriptors;
- normalized view and routine metadata;
- table constraints and semantic supporting indexes;
- literal one-statement query files described by PostgreSQL; and
- symbolic type, relation, column, collation, operator, operator-class, and
  routine identities without generated physical OIDs.

Queries are not accepted from dynamic strings, query builders, or runtime
catalog discovery. Parameter names/nullability and result cardinality come
from the manifest; they are not PostgreSQL proofs. Result nullability is
conservative and widens to `Option` whenever non-null cannot be established.

## Lean value mapping

Built-in mappings:

| PostgreSQL type | Lean type |
| --- | --- |
| `bool` | `Bool` |
| `bytea` | `ByteArray` |
| `int2`, `int4`, `int8` | `Int16`, `Int32`, `Int64` |
| `oid` | `Int` |
| `float4`, `float8` | `Float` |
| `text`, `varchar`, `bpchar`, `name`, `"char"` | `String` |
| `json`, `jsonb`, `uuid` | `String` |
| `date` | `Std.Time.PlainDate` |
| `time` | `Std.Time.PlainTime` |
| `timestamp` | `Std.Time.PlainDateTime` |
| `timestamptz` | `Std.Time.Timestamp` |
| `numeric` | `Pg.PgNumeric` |
| `interval` | `Pg.PgInterval` |

Also supported:

- generated inductive enum values;
- generated proof-refined domains;
- `Pgx.Typed.PgArray α`, represented as `Array (Option α)`, for ordinary
  one-dimensional arrays;
- generated named-composite structures whose fields are always `Option`;
- `Pgx.Typed.PgRange α` and `Pgx.Typed.PgMultirange α`, including empty and
  finite/infinite bounds;
- character length, numeric precision/scale, temporal precision, and interval
  precision refinements where the runtime mapping supports them; and
- explicit `ResolvedCodec` overrides, optionally grouped by installed
  PostgreSQL extension.

Not supported without an exact custom override:

- unknown base or extension types;
- pseudo-types as query values; and
- nested or multidimensional PostgreSQL arrays.

An override supplies a trusted encoder/decoder. It does not cause Lean to
derive the external type's semantic laws.

## Local constraints and refinements

PostgreSQL parses DDL and resolves names. `lean-pgx` then strictly parses a
normalized `pg_get_constraintdef(..., true)` expression into its own typed
constraint IR. SQL three-valued check behavior is preserved: only `false`
violates a check; `true` and `unknown` pass.

The executable subset includes:

- `IS NULL` and `IS NOT NULL`;
- Boolean `AND`, `OR`, and `NOT`;
- fixed-width integer comparisons;
- Boolean and enum equality;
- character length;
- one-argument `btrim`;
- `POSITION`;
- nested domains;
- modeled type modifiers; and
- casts proved not to change the modeled value.

Generated domains and query rows expose `Data`, `ValidPred`, proof-bearing
`Value`/`Row`, `validate`, `validate_sound`, and `validate_complete` forms as
applicable. Decoding revalidates these local predicates; invalid stored values
produce a typed constraint-violation error rather than a proof.

Explicitly rejected or omitted cases include:

- user-defined functions and operators;
- `NO INHERIT` table checks;
- exact `bpchar` check semantics;
- numeric arithmetic or comparison inside local checks; and
- casts into constrained or type-modified domains.

Unsupported constructs fail generation with a categorized, source-offset
diagnostic. They are not approximated as a stronger Lean proposition.

### Query propagation

Domain refinements remain value-local and may propagate through present values
in nullable results. A same-row table check propagates only when every column
identity it references is projected directly and generic-plan analysis proves
one non-outer occurrence of that relation. Self-join ambiguity, outer-join
synthetic nulls, expressions, or incomplete provenance prevent propagation.

## Runtime checks

Attachment:

- installs `search_path`, UTC timezone, UTF-8 client encoding, and standard
  conforming string settings;
- checks the server major and generated session contract;
- resolves symbolic types and relations to local OIDs;
- verifies schemas, relations, columns, domains, composites, arrays, ranges,
  multiranges, constraints, semantic indexes, views, routines, required
  extensions, and codec-package provenance; and
- returns `CheckedConnection database` only after those checks succeed.

On first use, each generated query prepares a deterministic named statement,
supplies resolved parameter OIDs, and verifies parameter/result descriptors.
Every execution verifies the returned columns before decoding.

Cardinality behavior:

| Manifest contract | Runtime result |
| --- | --- |
| `execute` | `Pgx.Typed.CommandResult` and no returned data rows |
| `exactlyOne` | one `Row`, otherwise a cardinality error |
| `zeroOrOne` | `Option Row`, otherwise a cardinality error |
| `many` | buffered `Array Row` |

`execute` preserves PostgreSQL's command tag, but does not infer an affected-row
count contract from it. Ordinary performance-only indexes do not block
attachment. Semantic unique, primary-key, and exclusion indexes do.

Attachment assumes checked schema objects do not change while its catalog
checks run. A checked capability can also be invalidated by changing its raw
connection's session settings or prepared statements.

## Relational logic

Implemented:

- a pure finite many-sorted state with duplicate-preserving row occurrences;
- generated schema/table tags, row membership (`At`) and occurrence membership
  (`OccAt`);
- explicit SQL equality, collation, and operator semantics supplied through a
  generated `Semantics` record;
- catalog lifecycle metadata and `IntegrityContext` selection;
- `Holds` propositions for column-key `UNIQUE`, including `NULLS NOT DISTINCT`;
- primary keys;
- `MATCH SIMPLE` and `MATCH FULL` foreign keys when the referenced relation is
  included in the generated state;
- column-only exclusion constraints; and
- pure one-occurrence insert, delete, and update specifications.

`IntegrityContext` contains supported relational constraints that are enforced,
validated, and due at the selected catalog-default phase. It is not a combined
predicate for local `CHECK`, `NOT NULL`, or domain validation.

Not implemented:

- analyzed query relational AST or bag semantics;
- generated relational `LocalPred`, `ScopedPred`, or exact-result `ResultPred`;
- snapshot-scoped observation APIs or `SnapshotM`;
- reification/certification of a live database as a Lean state;
- a theorem connecting query results or attachment to a logical state;
- `MATCH PARTIAL`, temporal `PERIOD`/`WITHOUT OVERLAPS`, expression exclusion
  keys, or references outside the generated state;
- cascades, `SET NULL`, `SET DEFAULT`, triggers, or generated-column effects;
- multi-row statement transitions;
- transaction-local `SET CONSTRAINTS`, concurrency, or isolation semantics;
  and
- independent `Holds` propositions for standalone indexes.

These boundaries matter: the relational API is a pure specification layer, not
a verified model of live PostgreSQL execution.
