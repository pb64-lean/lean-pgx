# ADR 0002: Executable local refinements

- Status: Accepted and implemented for a conservative subset
- Decision owners: `lean-pgx` maintainers

## Context

PostgreSQL domains, column type modifiers, `NOT NULL`, and table/domain `CHECK`
constraints can describe useful facts about one value or one row. Exposing
those facts as Lean subtypes can move validation and reasoning into application
code. Doing so unsafely, however, would be worse than exposing an unrefined
type: a generated proof must not come from an unchecked assertion that the
database is valid.

PostgreSQL check expressions use SQL three-valued logic and a very broad,
extensible expression language. User functions, operators, collations, domain
casts, and type-specific behavior cannot be approximated by superficially
similar Lean operations. Query projections introduce another hazard: columns
from different aliases or synthetic outer-join nulls must not be mistaken for
one source row satisfying a table check.

## Decision

Generate executable local refinements only for expressions translated exactly
into a typed internal constraint language.

1. PostgreSQL remains responsible for parsing DDL and name/type resolution.
2. The probe obtains normalized `pg_get_constraintdef(..., true)` source.
3. A strict parser accepts only the modeled expression subset and records typed
   value/truth expressions with source-offset diagnostics.
4. Evaluation preserves PostgreSQL check semantics: `false` fails, while
   `true` and `unknown` pass.
5. Generated value and row namespaces separate freely constructible `Data`
   from the proof-bearing `Value` or `Row` subtype.
6. `validate` executes the generated checks and returns either a named
   `ConstraintViolation` or a subtype proof.
7. Lean checks `validate_sound` and `validate_complete` relative to the emitted
   `ValidPred`.
8. Runtime decoding invokes generated validators again; it never inserts an
   axiom asserting that stored data satisfies the predicate.

The initial exact subset includes null tests, Boolean connectives, fixed-width
integer comparisons, Boolean/enum equality, character length, one-argument
`btrim`, `POSITION`, nested domains, supported type modifiers, and casts whose
modeled value is unchanged.

Domain refinements propagate value-locally. Same-row table checks propagate to
a query row only when result descriptors establish every referenced direct
column identity and generic-plan inspection establishes one non-outer
occurrence of that relation. Any incomplete or ambiguous provenance prevents
the refinement.

Global relational properties such as uniqueness and foreign keys do not refine
one row. They belong to the separate relational state model.

## Consequences

Positive consequences:

- proof-bearing values are constructed by executable checks rather than a
  database-validity axiom;
- application code can validate data before encoding it;
- invalid stored data is surfaced as a typed runtime failure;
- SQL `NULL` behavior is not collapsed into two-valued Boolean logic; and
- query refinement propagation is conservative around joins and aliases.

Costs and limitations:

- the parser intentionally rejects much of PostgreSQL's expression language;
- normalized PostgreSQL rendering and the translation/emitter remain trusted;
- `bpchar`, numeric arithmetic/comparison, user functions/operators,
  `NO INHERIT`, and constrained/type-modified domain casts are not currently
  modeled;
- adding an operation requires exact type, null, error, and collation semantics;
  and
- a local proof says nothing by itself about another row, a database snapshot,
  or a live server's global integrity.

## Extension rule

A new local construct may be accepted only when its PostgreSQL typing and
three-valued behavior have an exact internal representation, executable
evaluator, generated predicate, proof/tests, and failure diagnostics. Otherwise
generation must reject it explicitly rather than weaken or strengthen the
meaning silently.
