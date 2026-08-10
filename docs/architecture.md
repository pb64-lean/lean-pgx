# Architecture

`lean-pgx` separates server-authoritative SQL analysis from a small generated
runtime surface and from pure Lean propositions. The separation is deliberate:
PostgreSQL remains the authority on PostgreSQL syntax and catalog semantics,
while generated code uses stable symbolic identities and checks observations
before trusting wire values.

## Build-time pipeline

```text
declared migrations ─┐
literal queries ─────┼─► transient PostgreSQL ─► catalog/protocol probe
query manifest ──────┘                               │
                                                    ▼
                                       normalized symbolic DatabaseIR
                                                    │
                         ┌──────────────────────────┼─────────────────────┐
                         ▼                          ▼                     ▼
                  generated Lean             .pgir.json        contract hashes
```

The Bazel action:

1. creates a private temporary cluster with the pinned PostgreSQL distribution;
2. listens on an action-private Unix-domain socket;
3. uses a pinned `socat` loopback bridge because the current `pg-lean` client
   surface connects over TCP;
4. replays declared migrations in order;
5. asks PostgreSQL to parse and describe literal statements and reads normalized
   catalog metadata;
6. converts physical OIDs into symbolic identities;
7. validates the manifest and the supported semantic subset;
8. emits fixed Lean and contract artifacts; and
9. stops both bridge and server and removes the temporary cluster.

The action declares server, bridge, lifecycle, migration, query, manifest, and
generator inputs and requests Bazel's `block-network` execution requirement.
Actual enforcement of that request depends on the selected Bazel executor.
The private server and loopback bridge are build tools, not application runtime
dependencies.

## Why PostgreSQL is authoritative

Reimplementing PostgreSQL parsing, overload resolution, casts, collation rules,
and result description would create a competing SQL implementation. Instead,
the generator delegates those operations to a pinned real server and retains
only normalized facts required by Lean generation and later drift checks.

Two manifest facts remain application-owned:

- parameter nullability, because PostgreSQL's statement description does not
  provide the intended input contract; and
- result cardinality, because statement description does not prove how many
  rows a query returns.

Both are checked at the available boundary: parameter optionality controls the
generated encoder, while cardinality is enforced after execution.

## Canonical IR and fingerprints

`DatabaseIR` represents schemas, types, relations, constraints, semantic
indexes, views, routines, extension provenance, and described queries. It uses
qualified names and structural keys rather than installation-local OIDs.
Ordering is canonicalized before serialization and hashing.

The generation target emits:

- `<name>.pgir.json`, the canonical snapshot;
- `<name>.contract.sha256`, the canonical-major runtime contract fingerprint;
  and
- `<name>.compatibility.sha256`, a major-independent fingerprint.

The JSON snapshot currently carries an explicit `formatVersion`, and its reader
retains compatibility with earlier development versions. It is nevertheless a
diagnostic/build artifact rather than a stable interchange format before 1.0.
Consumers should prefer the generated Lean API or documented Bazel providers
unless they explicitly accept pre-release `.pgir.json` format changes.

`pg_compat_test` replays the same inputs under each selected PostgreSQL major
and compares normalized semantics, not raw catalog rows or OIDs.

## Generated layers

For module prefix `AppDb`, generation emits:

```text
AppDb/Types.lean
AppDb/Schema.lean
AppDb/Constraints.lean
AppDb/Queries/<Query>.lean
AppDb.lean
```

- `Types` contains generated enums, domains, composites, and value codecs.
- `Schema` contains typed relation data and descriptor declarations.
- `Constraints` contains normalized metadata and local validator definitions.
- each `Queries` module contains `Params`, `Row`, descriptors, encoder/decoder,
  and a cardinality-specific `run` function;
- the root exposes `database`, `attach`, and the generated relational logic
  namespace.

Generated imports include `Pgx.Typed`, local constraint semantics, and the pure
logic kernel. Additional imports and Bazel dependencies come from declared type
overrides.

## Runtime capability

`attach` converts `Pg.Connection` into
`CheckedConnection AppDb.database` only after installing the generated session
settings, resolving symbolic catalog objects, and comparing descriptors. The
dependent type prevents a checked capability for one generated database from
being passed to a query for another.

Query preparation is lazy and cached. The cache key includes database and query
contract hashes plus SQL. Before binding, runtime code compares prepared
parameter and result descriptors. Before decoding each result set, it checks
the returned column descriptors again. Local refined values are constructed
only by their generated validators.

This capability assumes exclusive respect for its invariants: callers must not
mutate the raw session contract, deallocate cached statements, or alter schema
objects behind it.

## Proof and specification layers

Local refinements are executable predicates over one value or one row. Their
validators return proof-bearing subtypes and carry soundness/completeness
theorems relative to the generated predicate.

Relational constraints require multiple rows. They are represented separately
over a finite, immutable, duplicate-preserving many-sorted `State`. Generated
`Semantics` inputs make SQL equality, collation, and exclusion operators
explicit. `Holds` and mutation specs are pure propositions; runtime attachment
does not create their proofs or assert that a live server equals a logical
state.

See the design decisions for the rationale and the
[trust document](assurance-and-trust.md) for the assurance boundary.
