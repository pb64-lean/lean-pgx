# ADR 0003: Duplicate-preserving relational state model

- Status: Accepted; foundational subset implemented
- Decision owners: `lean-pgx` maintainers

## Context

Unique, primary-key, foreign-key, and exclusion constraints are propositions
about multiple rows. They cannot soundly inhabit an individual generated row
type. Query reasoning also needs SQL bag behavior: two equal row values can
occur separately, and deleting one occurrence must not delete every equal
value.

PostgreSQL constraint equality is not Lean structural equality. It depends on
SQL null rules, `NULLS NOT DISTINCT`, collations, operator classes, foreign-key
operator vectors, and exclusion operators. Constraint lifecycle also matters:
unenforced, unvalidated, deferrable, and initially deferred states cannot all be
treated as an immediate whole-state invariant.

The design must support pure reasoning without pretending that runtime
attachment has read or certified all database rows.

## Decision

Represent relational semantics in a pure generated namespace over a reusable
many-sorted kernel.

### State and membership

- A generated `Table` tag identifies each relation-shaped object.
- `Row : Table → Type` maps each tag to its generated row data.
- `State` stores a finite array of row occurrences for every table.
- `RowAt state table row` expresses value membership.
- `OccAt state table occurrence` preserves a particular array occurrence and
  its identity.

Arrays deliberately model bags. Proofs about uniqueness/exclusion compare
distinct occurrences, not merely unequal Lean values.

### Explicit SQL semantics

Code generation emits typed key projections and a `Semantics` record. Its
fields interpret the exact comparison/operator obligations captured from the
catalog. Live attachment does not manufacture a semantics value or prove its
laws. Callers must supply the interpretation used by a pure proof.

### Generated constraint propositions

The implemented subset emits lifecycle metadata and `Holds` for:

- column-key unique constraints, including `NULLS NOT DISTINCT`;
- primary keys;
- `MATCH SIMPLE` and `MATCH FULL` foreign keys whose referenced table is in
  the generated state; and
- column-only exclusion constraints.

Unsupported relational constraints are retained in a generated inventory with
a reason. Expression-based exclusion keys, `MATCH PARTIAL`, temporal
`PERIOD`/`WITHOUT OVERLAPS`, and out-of-state references are not approximated.

`IntegrityContext semantics phase state` collects only modeled constraints that
are enforced, validated, and due at the selected catalog-default lifecycle
phase. It does not duplicate local `CHECK`, `NOT NULL`, or domain predicates.

### Mutation specifications

Each modeled table receives pure insert, delete, and update relations for one
row occurrence. They describe the before/after state change and selected
integrity obligations. They do not execute SQL or claim equivalence with
PostgreSQL DML.

## Consequences

Positive consequences:

- global constraints are separated from local proof-bearing row values;
- duplicate identity is available for correct bag/uniqueness reasoning;
- equality, null, collation, and operator assumptions are explicit inputs;
- lifecycle metadata prevents indiscriminate use of deferred or unvalidated
  constraints; and
- pure mutation specifications provide a base for later transaction reasoning.

Costs and limitations:

- constructing useful `Semantics` values and proving their laws is application
  or future library work;
- no current runtime operation proves that a live database corresponds to a
  generated `State`;
- standalone indexes are descriptors, not independent `Holds` propositions;
- transition specs omit cascades, `SET NULL`, `SET DEFAULT`, triggers,
  generated columns, multi-row statements, and transaction-local constraint
  timing; and
- concurrency and isolation are outside the current model.

## Deferred query and snapshot layer

The state kernel is designed to support, but does not yet include:

- a bounded analyzed query AST with duplicate-preserving denotation;
- generated local/scoped/exact-result predicates;
- nominal snapshot scopes and an observation monad;
- state reification or certification from a live transaction; or
- a theorem connecting live query execution to pure relational denotation.

Those features require an explicit trust and isolation story. They must not be
inferred merely from successful schema attachment.
