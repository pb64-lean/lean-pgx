# Roadmap

This roadmap describes direction, not a release promise. Scope and ordering
may change as PostgreSQL behavior is modeled and tested.

## Delivered foundation

The delivered foundation consists of:

- server-authoritative DDL/query probing, symbolic IR, generated checked
  queries, compatibility tests, and attachment-time drift detection;
- typed local constraint semantics with proof-producing validation;
- broader PostgreSQL value shapes, type modifiers, extension codecs, and
  conservative refinement propagation; and
- a duplicate-preserving many-sorted relational state kernel with generated
  propositions for a conservative constraint subset and pure single-row
  transition specifications.

The precise implemented boundary is maintained in
[`docs/support.md`](docs/support.md).

## Future themes

### Q1 — Query semantic IR

- Add an analyzed relational query representation for a deliberately bounded
  SQL fragment.
- Define bag-preserving denotation over generated logical states.
- Generate local, scoped, and exact-result predicates only where analysis is
  complete and sound.
- Keep unsupported plans and expressions explicit rather than approximating
  them as stronger guarantees.

### S1 — Snapshot observations

- Introduce nominal snapshot scopes and a `SnapshotM`-style API.
- Tie rows observed together to one logical snapshot without allowing proofs
  to escape their scope.
- Specify interaction with PostgreSQL isolation levels and statement versus
  transaction snapshots.

### C1 — State certification

- Design an explicit reification/certification path from live observations to
  finite Lean state.
- Define what is read, under which locks or isolation mode, and which trusted
  assumptions remain.
- Separate checked catalog attachment from certification of row contents and
  relational integrity.

### T1 — Transaction and mutation semantics

- Extend beyond one-occurrence abstract insert/delete/update relations.
- Model multi-row statements, deferred constraints, `SET CONSTRAINTS`, foreign
  key actions, generated columns, and selected trigger behavior.
- State concurrency and isolation assumptions explicitly before connecting
  transition proofs to live DML.

### Coverage and hardening

- Expand local expression support where PostgreSQL semantics can be modeled
  exactly, including additional operators and value families.
- Add supported relational cases such as safe expression keys or additional
  foreign-key forms only with explicit operator/collation semantics.
- Establish a published release process, compatibility policy, and artifact
  provenance story while maintaining the exact assurance inventory.
