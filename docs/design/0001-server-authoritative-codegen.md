# ADR 0001: Server-authoritative code generation

- Status: Accepted and implemented
- Decision owners: `lean-pgx` maintainers

## Context

A typed PostgreSQL client needs parameter and result types, nullability,
relation/type identity, and enough schema semantics to detect when generated
code no longer matches deployment. PostgreSQL's behavior depends on its own
parser, analyzer, catalogs, overload resolution, casts, collations, extensions,
and server version.

Maintaining a second SQL analyzer in Lean would create a large compatibility
surface and could disagree with the database precisely where generated types
must be trustworthy. Capturing raw OIDs is also unsuitable because OIDs are
installation-local. Reading a developer database during a normal build would
make generation non-hermetic and could expose or depend on mutable state.

PostgreSQL statement description still cannot infer two application-level
contracts safely: the intended nullability of each input and the number of rows
the application expects.

## Decision

Generation is server-authoritative and input-replay based.

1. Bazel starts an empty cluster from a pinned PostgreSQL distribution.
2. The action replays only declared migration files, in order.
3. Every declared query is a literal one-statement `.sql` file.
4. PostgreSQL parses, resolves, plans/describes, and exposes normalized catalog
   metadata for those inputs.
5. A small manifest supplies query names, input nullability, result cardinality,
   supported server majors, and explicit custom codecs.
6. The probe translates physical observations into canonical symbolic IR.
   Qualified type/relation/operator/routine identities replace OIDs.
7. The emitter writes a fixed set of Lean modules, a JSON IR snapshot, and
   canonical/compatibility fingerprints.
8. A generated `attach` function resolves symbolic identities against each live
   connection and checks the supported catalog/session contract.
9. Each query verifies prepared parameter/result descriptors and returned
   columns before encoding or decoding.

Generation defaults to PostgreSQL 18 as the canonical server; PostgreSQL 17 is
also selectable. A compatibility rule can replay the same inputs on both and
compare normalized major-independent semantics.

The build action requests a network-blocked executor and confines its database
to a private Unix socket. A pinned loopback bridge exists only because the
current client transport connects over TCP. No ordinary build step contacts a
developer or production database.

## Consequences

Positive consequences:

- generated SQL typing follows the selected real PostgreSQL implementation;
- schema construction is reproducible from reviewable build inputs;
- output does not depend on installation-local OIDs;
- cross-major differences become explicit test failures;
- runtime drift is reported before affected bytes are decoded; and
- application code receives a database-indexed checked capability.

Costs and limitations:

- builds require Nix and executable PostgreSQL tooling;
- generation is heavier than pure source translation;
- PostgreSQL, probe queries, protocol observations, normalization, and emission
  stay inside the trust boundary;
- parameter nullability and result cardinality remain manifest assertions;
- network isolation ultimately depends on Bazel executor enforcement; and
- attachment detects the modeled descriptor surface, not arbitrary concurrent
  DDL or row-level integrity.

## Rejected alternatives

### Implement a complete independent SQL analyzer

Rejected because the effort and semantic divergence risk are disproportionate,
especially across PostgreSQL versions and extensions.

### Generate from a shared development database

Rejected because mutable external state breaks reproducibility, reviewability,
and safe build isolation.

### Embed observed OIDs in generated code

Rejected because restore order, extension installation, and cluster history can
change OIDs without changing the symbolic schema.

### Trust generated descriptors without live checks

Rejected because application binaries and migrations can be deployed out of
step. Attachment and per-query verification are part of the contract, not an
optional diagnostic mode.
