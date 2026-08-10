# Assurance and trust

`lean-pgx` combines proof-checked Lean code with observations made by a real
PostgreSQL server and with ordinary generator/runtime software. It is important
to distinguish what the Lean kernel checks from what the system tests or
assumes.

## What Lean checks

For supported local refinements, generated code defines a predicate and a
validator that returns a proof-bearing subtype. Lean checks the generated
proofs and the stated `validate_sound`/`validate_complete` theorems relative to
that generated predicate.

For the relational layer, Lean checks definitions and theorems over the pure
finite state model. This includes duplicate-sensitive membership and the
generated propositions/specifications for the supported relational constraint
forms.

Lean's type checker also enforces that a generated query receives a
`CheckedConnection` indexed by the same generated database descriptor.

## Trusted and tested components

The current trusted computing boundary includes:

- PostgreSQL's SQL parser, analyzer, catalogs, descriptor behavior, and wire
  behavior;
- the pinned PostgreSQL binaries and Nix/Bazel execution environment;
- `pg-lean` protocol parsing, connection behavior, and codecs;
- catalog probe queries and version adapters;
- normalization from physical catalog data to symbolic IR;
- the strict parser for normalized PostgreSQL `CHECK` expressions;
- type mapping, projection/provenance analysis, code generation, and emission;
- generated encoders/decoders and custom `ResolvedCodec` implementations; and
- runtime catalog I/O, attachment checks, preparation, execution, and result
  verification.

These components are exercised by unit, generation, compatibility, and live
PostgreSQL tests. Testing reduces risk but does not move them outside the trust
boundary.

## What attachment establishes

A successful generated `attach` establishes, according to the trusted runtime
checks, that the connection has the expected session settings and that the
observed catalog objects match the generated symbolic descriptor. It resolves
local OIDs, verifies supported schema semantics and extension provenance, and
creates a database-indexed capability.

The first execution of each query verifies prepared parameter/result
descriptors. Every execution verifies result columns before decoding. Local
refined values are validated again while decoding.

Attachment is drift detection, not a proof about all rows, future catalog
states, PostgreSQL implementation correctness, or concurrent changes.

## What is not established

The current implementation does not establish:

- that PostgreSQL implements its documented semantics correctly;
- that a live database's rows are represented by a particular pure `State`;
- that relational `Holds` propositions are true of live data;
- that a query's result is the denotation of a generated relational AST;
- that concurrent DDL cannot race attachment checks;
- transaction, snapshot, isolation, trigger, or foreign-key action correctness;
- correctness of application-provided type codecs; or
- end-to-end formal verification from SQL source through network I/O.

Do not treat generated `At`, `OccAt`, `Holds`, or mutation propositions as live
database certificates. They are specification tools until an explicit
observation/certification mechanism is implemented.

## Axioms and assurance policy

Local subtype proofs are built from executable generated predicates; runtime
decoding does not insert an axiom asserting database validity.

`//lean:pgx_assurance` applies rules_lean's exact assurance policy to every
`Pgx` module reachable through the public facade. It pins the allowed standard
axioms, principal theorem statements, partial-definition inventory, absence of
unsafe/extern/opaque declarations, and native targets inherited from the
separately audited pg-lean/TLS dependency stack. Any change to that inventory
must update the reviewed policy explicitly.

This is a declaration and dependency audit, not a proof that the trusted
probe, emitter, codecs, PostgreSQL, or runtime I/O implement their intended
semantics. Claims remain limited to the checked definitions and boundaries
described above.

## Operational assumptions

After attachment, the caller must preserve the checked capability's invariants:

- keep the generated session settings intact;
- do not deallocate or replace cached generated statements through the raw
  connection;
- do not alter checked schema objects behind the connection; and
- close the underlying `Pg.Connection` according to application ownership.

Security issues involving these boundaries should be reported through
[`SECURITY.md`](../SECURITY.md).
