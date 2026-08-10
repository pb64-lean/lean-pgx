# lean-pgx

`lean-pgx` generates checked Lean 4 records and query runners from PostgreSQL
DDL and literal SQL. PostgreSQL itself performs SQL parsing, name resolution,
cast selection, and result description; generated code stores only symbolic
schema/type identities and verifies the live descriptors before decoding.

The current implementation includes:

- deterministic schema/query IR for schemas, enums, domains, arrays,
  composites, ranges, multiranges, tables, views, routines, constraints,
  indexes, parameters, result columns, and cardinality;
- a pinned PostgreSQL 18.2 generation action and PostgreSQL 17.8 compatibility
  test;
- generated enum codecs, proof-refined domains, `Params`, proof-refined `Row`
  values, and checked runners;
- a typed local-constraint IR with PostgreSQL three-valued Boolean semantics,
  proof-producing domain/row validators, and soundness/completeness theorems;
- provenance-checked propagation of domain and same-row `CHECK` refinements
  through complete direct query projections;
- conservative result nullability (`Option` whenever non-null cannot be
  established);
- runtime symbolic OID resolution, schema attachment, prepared-descriptor
  verification, and typed `SchemaDrift`/`QueryDrift` errors;
- generated one-dimensional arrays of built-in and generated values, named
  composite cells, and range/multirange values with resolver-aware codecs;
- local character, exact numeric precision/scale, temporal precision, and
  interval precision refinements, propagated through generated arrays,
  composites, and finite range/multirange bounds;
- reusable extension codec packages whose installed version and owned types
  are recorded in the generated contract;
- local revalidation during decoding, reported as typed constraint-violation
  errors when stored data does not establish the generated proposition;
- normalized symbolic metadata for unique, primary-key, foreign-key, and
  exclusion constraints and their semantic supporting indexes;
- a pure, duplicate-preserving, many-sorted relational state kernel with
  generated state-indexed `At`/`OccAt` aliases, relational `Holds`
  propositions, lifecycle-aware integrity contexts, and abstract
  insert/delete/update specifications;
- explicit type overrides and hard generation errors for unsupported types.

## Bazel usage

The build expects `rules_lean`, `pg-lean`, and `tls13-lean` as sibling
checkouts. The local module pins PostgreSQL, `socat`, and the action lifecycle
utilities through one Nix revision; the ordinary build does not use a
developer or production database.

```starlark
load(
    "@lean-pgx//bazel:defs.bzl",
    "lean_pg_library",
    "pg_compat_test",
    "pg_query_set",
)

pg_query_set(
    name = "queries",
    srcs = [
        "queries/get_user.sql",
        "queries/list_users.sql",
    ],
    manifest = "queries/queries.json",
)

lean_pg_library(
    name = "app_db",
    module_prefix = "AppDb",
    migrations = [
        "migrations/0001_schema.sql",
        "migrations/0002_tables.sql",
    ],
    queries = ":queries",
    schemas = ["app"],
)

pg_compat_test(
    name = "app_db_pg17_pg18",
    database = ":app_db",
    postgres = [
        "@postgresql_17//:toolchain",
        "@postgresql_18//:toolchain",
    ],
)
```

Each query file must contain one statement. Its manifest entry supplies the
Lean module name, parameter names/nullability, and runtime-checked cardinality;
PostgreSQL infers all SQL types.

```json
{
  "supportedServerMajors": [17, 18],
  "get_user.sql": {
    "leanName": "GetUser",
    "cardinality": "zeroOrOne",
    "parameters": [
      {"position": 1, "name": "id", "nullable": false}
    ]
  }
}
```

The declared generation outputs are fixed:

```text
AppDb/Types.lean
AppDb/Schema.lean
AppDb/Constraints.lean
AppDb/Queries/GetUser.lean
AppDb/Queries/ListUsers.lean
AppDb.lean
app_db.pgir.json
app_db.contract.sha256
app_db.compatibility.sha256
```

The action initializes a private cluster, makes PostgreSQL listen only on an
action-private Unix-domain socket, replays the declared migrations in order,
probes the declared schemas and queries, writes those outputs, and stops the
server. The PostgreSQL client dependency currently exposes TCP connections,
so a pinned `socat` process bridges a random loopback port to that private
socket for the duration of the action. Bazel blocks external networking, all
server/bridge/lifecycle tools are declared inputs, and cleanup stops both
processes and removes the private cluster.

## Generated runtime API

```lean
import AppDb

def findUser
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (id : Int64) :
    Std.Async.Async
      (Except Pgx.Typed.Error (Option AppDb.Queries.GetUser.Row)) :=
  AppDb.Queries.GetUser.run conn { id }
```

Obtain the checked capability from a raw `Pg.Connection`:

```lean
let checked ← AppDb.attach raw
```

Attachment installs and verifies the generated session contract, checks the
server major, resolves every symbolic type/relation against local OIDs, and
compares schema descriptors, including array elements, composite fields, and
complete range metadata (subtype, multirange link, collation, subtype operator
class, canonical routine, and subtype-difference routine). It also compares
normalized view/routine metadata, extension package ownership, and relation
constraints, including validation/enforcement/deferral, foreign-key actions
and operator vectors, inheritance/period facts, and supporting-index identity.
Semantic unique, primary-key, and exclusion indexes are compared with their
key expressions, collations, operator classes, equality operators, null
policy, predicates, and readiness/validity flags. Ordinary performance-only
indexes are not attachment blockers. Each query's first use prepares with
resolved parameter OIDs and compares the returned parameter/result descriptors
before binding or decoding.

PostgreSQL 18 native `NOT NULL` constraints that are unvalidated or unenforced
are rejected during generation and attachment: `attnotnull` alone is not a
sound promise that pre-existing rows are non-null in that transitional state.

Generated container values use these runtime shapes:

```lean
Pgx.Typed.PgArray α       -- Array (Option α), one dimension
Pgx.Typed.PgRange α       -- empty or finite/infinite typed bounds
Pgx.Typed.PgMultirange α  -- Array (PgRange α)
```

A named PostgreSQL composite becomes a generated structure. Every composite
field is an `Option`: table `NOT NULL` constraints do not constrain a row-type
value used independently. `AppDb.Constraints.views` and
`AppDb.Constraints.routines` expose normalized view and overload/table-result
metadata captured from PostgreSQL.

Generated domains and row-returning queries separate freely constructible
`Data` from their proof-bearing public value:

```lean
def ValidPred : Data → Prop
def validate : Data → Except Pgx.ConstraintViolation Row
theorem validate_sound ...
theorem validate_complete ...
```

`CHECK` evaluation is performed again in Lean. As in PostgreSQL, only SQL
`false` violates a check; `true` and `unknown` both pass. No database axiom is
used to construct the subtype proof. Unique, primary-key, foreign-key, and
exclusion guarantees still do not refine an individual row. They are emitted
instead as propositions over `AppDb.Logic.State`; generated `At` aliases
package positive row membership, while `OccAt` preserves duplicate occurrence
identity for uniqueness and exclusion reasoning.

## Relational logic API

`AppDb.Logic` defines a finite, immutable logical state whose tables are arrays
of row occurrences. For every modeled relational constraint, code generation
emits typed key projections, catalog lifecycle metadata, and a `Holds`
proposition. SQL equality, null, collation, and operator behavior is supplied
explicitly through `AppDb.Logic.Semantics`; neither attachment nor a live query
manufactures these semantics or a proof that a logical state represents
PostgreSQL.

Generated propositions currently cover column-key `UNIQUE` constraints,
including `NULLS NOT DISTINCT`; primary keys; `MATCH SIMPLE` and `MATCH FULL`
foreign keys whose referenced relation is present in the generated state; and
column-only exclusion constraints. `unsupportedRelationalConstraints` records
conservative omissions such as `MATCH PARTIAL`, temporal
`PERIOD`/`WITHOUT OVERLAPS`, expression-based exclusion keys, and references
outside the generated state.

`IntegrityContext` includes only modeled relational constraints that are
enforced, validated, and due at the selected catalog-default phase. It is not
a predicate for every local `CHECK`, `NOT NULL`, or domain constraint.
Generated `insertSpec`, `deleteSpec`, and `updateSpec` declarations are pure,
one-occurrence state-transition specifications, not live DML operations or
backend-correctness theorems.

Analyzed query/K-relational semantics, relational `LocalPred`, `ScopedPred`,
and exact-bag `ResultPred` contracts, nominal snapshot scopes, `SnapshotM`,
state reification/certification, and any theorem connecting a live PostgreSQL
observation to a logical `State` are not yet implemented. Mutation specs do
not yet model cascades, `SET NULL`/`SET DEFAULT`, triggers, generated-column
effects, multi-row statements, transaction-local `SET CONSTRAINTS`,
concurrency, or isolation semantics. Standalone indexes receive no `Holds`
proposition, and attachment assumes the schema is not concurrently modified
while its catalog checks run.

The executable subset covers null tests, Boolean connectives, fixed-width
integer comparisons, Boolean and enum equality, character length, one-argument
`btrim`, `POSITION`, nested domains, and casts whose modeled values are proved
unchanged. Generation reports a categorized source-offset diagnostic for
unsupported constructs. In particular, user-defined functions/operators,
`NO INHERIT`, `bpchar` check semantics, numeric arithmetic, and casts into a
constrained or type-modified domain are rejected instead of approximated.

Table checks propagate to a query row only when result descriptors establish
every referenced identity projection and generic-plan inspection establishes
exactly one non-outer occurrence of that relation. This prevents synthetic
outer-join nulls and columns from different self-join aliases from being
treated as one source row. Domain validation remains value-local, so present
domain values can still be refined in nullable outer-join results.

The generated runners map cardinality to results as follows:

| Manifest value | Lean result |
| --- | --- |
| `execute` | `Pgx.Typed.CommandResult` |
| `exactlyOne` | `Row` |
| `zeroOrOne` | `Option Row` |
| `many` | `Array Row` |

## Type overrides and extension packages

Unknown base/extension types and pseudo-types are rejected unless the manifest
declares an override:

```json
{
  "typeOverrides": [
    {
      "key": {"schema": "ext", "name": "vector", "kind": "base"},
      "leanType": "MyVector.Vector",
      "codec": "MyVector.codec",
      "importModule": "MyVector"
    }
  ]
}
```

The `codec` declaration must have type
`Pgx.Typed.ResolvedCodec MyVector.Vector`; add its Bazel Lean target to the
`deps` of `lean_pg_library`.

When several codecs belong to one PostgreSQL extension, declare them as a
package. The package owns one import module, so nested overrides omit
`importModule`:

```json
{
  "extensionCodecPackages": [
    {
      "extension": "vector",
      "importModule": "PgVector",
      "typeOverrides": [
        {
          "key": {"schema": "public", "name": "vector", "kind": "base"},
          "leanType": "PgVector.Vector",
          "codec": "PgVector.codec"
        }
      ]
    }
  ]
}
```

Generation requires that extension to be installed, resolves its installed
version, rejects overlapping package ownership, and records deterministic
package provenance alongside the resolved overrides.

## Build and tests

```sh
bazel build //...
bazel test //...
```

The end-to-end fixture in `examples/app_db` exercises DDL replay, all four
cardinalities, enum/domain arrays, composite cells, ranges/multiranges,
numeric/time modifiers, view and table-valued-function metadata,
conservative outer-join nullability, shifted user OIDs, proof-producing local
validation, invalid stored-data rejection, runtime cardinality checks,
generated relational API compilation, `QueryDrift`, targeted semantic
`SchemaDrift` (including relational constraint lifecycle, semantic index
identity, range collation, operator-class, and subtype-difference changes), and
live PostgreSQL 17/18 compatibility.

Lake supplies the editor project model; Bazel remains authoritative:

```sh
lake update
lake build
```
