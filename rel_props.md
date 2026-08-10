The following is part of a design discussion related to this project. Grain of salt - the response was written without specific context of the lean-pgx repo structure.

====

Some PostgreSQL constraints have natural Lean proposition analogs, like `select * from person where name = 'foo'` giving a sequence of Person objects `p` with `p.name == "foo"` . Others effectively amount to quantified first-order logic propositions, e.g. if a query left joins one table against another and filters by some negative criterion on the other table, it would require quantifying over rows of that table in proposition form, as in "foo: Foo s.t. there does not exists a bar: Bar with foo.name == bar.name". Or at least, that seems natural at first, but the use of a table's record type to capture the set of rows in that table in a particular database state is not valid: the record type is inhabited by all constructible values definitionally. So we lack a representation of database snapshot state and a type family for the rows of a table at a given state. If we could refine a record datatype by these quantified relations and scope the claim to some contextual state, we could achieve usable quantified subtypes, but still the right approach is not obvious.
Research the possibilities and known approaches for FOL modeling of PostgreSQL queries requiring quantification in a scoped context. Combining the learnings with first-principles problem solving, propose and map out a suitable approach for our Lean 4 codegen.

----

# Recommendation

Lock in a **two-axis, state-indexed relational design**:

1. A value `s : DbState Schema` is the immutable logical database snapshot against which propositions are interpreted.
2. A nominal type parameter `σ` identifies the lifetime of a live PostgreSQL statement or transaction snapshot and prevents observations from unrelated snapshots from being mixed accidentally.

The generated table record remains the carrier of all representable row values. Actual rows are a state-indexed subtype:

```lean
Person.At s := { p : Person.Data // s.Mem .person p }
```

For query results, generate three progressively stronger contracts:

```lean
LocalPred  : Params → RowData → Prop
ScopedPred : DbState → Params → RowData → Prop
ResultPred : DbState → Params → Array RowData → Prop
```

* `LocalPred` contains consequences checkable from the returned row and parameters.
* `ScopedPred` contains quantified facts about a particular database state.
* `ResultPred` says that the whole returned bag is exactly the denotation of the query in that state.

The ordinary live PostgreSQL API should construct proofs of `LocalPred`. It should not silently manufacture proofs of `ScopedPred` or `ResultPred`. Those stronger proofs require either a reified finite state checked by Lean, a checkable database certificate, or an explicit backend-conformance assumption.

This is the central architectural choice.

---

# 1. Research synthesis

Classical database logic does not interpret a table name as a type. It interprets it as a relation inside a database instance. In a Lean presentation, `Bar.Data` may conveniently be a row sort, but the actual table is still a state-dependent relation predicate or multiplicity function over that sort.

Realistic SQL semantics adds several features that plain set-valued first-order logic does not capture directly:

* SQL relations and results are bags.
* correlated subqueries require an explicit binding environment;
* nulls require SQL-specific predicate semantics;
* outer joins must distinguish an absent right-hand row from a present row containing null fields.

Formal SQL semantics and subsequent Coq mechanizations model precisely these features, including bags, lateral and nested subqueries, scope, and nulls. HoTTSQL uses the closely related idea of a K-relation: a relation is a function from tuples to annotations, with natural-number annotations giving bag multiplicities. ([Informatics Homepages][1])

This leads to an important division of responsibilities:

* **K-relational semantics** should be the authoritative denotation of a query.
* **First-order propositions** should be derived from its positive-support semantics when possible.
* **Lean subtypes** should package useful consequences of those propositions.

One should not attempt to solve an arbitrary SQL verification problem during code generation. General SQL postcondition and equivalence checking is undecidable over finite databases; practical systems therefore restrict the logical fragment or use incomplete proof procedures. Cosette and related systems demonstrate that substantial automation is possible, but not that a complete SQL prover is available. ([arXiv][2])

Provenance research supplies another relevant distinction. Positive queries can often be justified by witness rows and successful derivations. Negation and difference require information about failed derivations or missing witnesses; there is no universal positive-semiring treatment of relational difference. This is the logical source of the “closed-world evidence” cost of `NOT EXISTS` and anti-joins. ([arXiv][3])

Finally, per-query propositions are not sufficient for programs that make several reads and writes. Hoare and Dijkstra monads model such operations through predicates over pre- and post-states. Lean's current predicate-transformer and `mvcgen` infrastructure is designed for stateful assertions and weakest-precondition reasoning, so it is a natural later layer rather than something that must be recreated inside every generated row type. ([arXiv][4])

---

# 2. The database snapshot as a finite many-sorted model

The generated schema should define a many-sorted signature:

```lean
namespace Pg.Logic

structure Schema where
  Table : Type
  Row   : Table → Type

end Pg.Logic
```

For the application schema:

```lean
namespace AppDb

inductive Table
  | person
  | foo
  | bar
deriving DecidableEq, Repr

def Row : Table → Type
  | .person => Person.Data
  | .foo    => Foo.Data
  | .bar    => Bar.Data

def schema : Pg.Logic.Schema where
  Table := Table
  Row   := Row

end AppDb
```

`Person.Data`, `Foo.Data`, and `Bar.Data` are carriers. Their inhabitants are possible values, not claims that any such value occurs in the database.

## 2.1 Bag-valued table interpretations

Use a finite-support natural-number K-relation:

```lean
namespace Pg.Logic

structure KRel (α : Type u) where
  mult : α → Nat
  finiteSupport : Set.Finite {x | mult x ≠ 0}

structure DbState (S : Schema) where
  rel : (t : S.Table) → KRel (S.Row t)

def DbState.Mem
    (s : DbState S)
    (t : S.Table)
    (r : S.Row t) : Prop :=
  0 < (s.rel t).mult r

end Pg.Logic
```

The denotational interface can be a multiplicity function. The executable representation should be array- or finite-map-backed and carry a theorem connecting that representation to `mult`.

This gives the requested state-indexed row type directly:

```lean
namespace Pg.Logic

abbrev RowAt
    (s : DbState S)
    (t : S.Table) :=
  { r : S.Row t // s.Mem t r }

end Pg.Logic
```

Generated aliases make it ergonomic:

```lean
namespace AppDb.Person

abbrev At (s : AppDb.State) :=
  Pg.Logic.RowAt s .person

end AppDb.Person
```

The logically correct anti-existence statement can then be written in either equivalent form:

```lean
¬ ∃ b : Bar.Data,
    s.Mem .bar b ∧ matches foo b
```

or:

```lean
¬ ∃ b : Bar.At s,
    matches foo b.val
```

Quantifying over `Bar.Data` was not intrinsically wrong. The missing component was the state-dependent relation-membership atom.

## 2.2 Occurrences as well as row values

`RowAt s t` deliberately forgets duplicate occurrences. This is harmless for ordinary existential or universal row predicates, but insufficient for exact bag results, uniqueness constraints, or counting.

Generate an occurrence type as well:

```lean
abbrev OccAt
    (s : DbState S)
    (t : S.Table) :=
  Σ r : S.Row t, Fin ((s.rel t).mult r)
```

If a value occurs three times, it contributes three inhabitants through `Fin 3`. This avoids physical PostgreSQL identifiers such as `ctid` while retaining the multiplicity needed by SQL semantics.

For example:

* a check constraint quantifies over `RowAt`;
* a foreign key usually quantifies over `RowAt`;
* a primary-key uniqueness proposition quantifies over `OccAt`;
* `COUNT(*)` and exact query results use multiplicities directly.

## 2.3 Integrity is a predicate on states

Do not define every state to be valid by construction:

```lean
def Integrity (phase : ConstraintPhase) (s : AppDb.State) : Prop :=
  ...
```

Query semantics should be defined for arbitrary finite states. Additional theorems may simplify that semantics under `Integrity phase s`.

This separation is required by PostgreSQL's actual constraint lifecycle:

* a `NOT VALID` constraint need not hold for existing rows;
* `pg_constraint` records whether a constraint is enforced and validated;
* deferrable uniqueness, primary-key, foreign-key, and exclusion constraints may be temporarily false before their checking point. ([PostgreSQL][5])

A useful generated structure is:

```lean
structure IntegrityContext
    (phase : ConstraintPhase)
    (s : AppDb.State) : Prop where
  personChecks : ...
  barNotNull   : ...
  fooBarFk     : ...
  ...
```

Only constraints that are supported, enforced, validated, and applicable at `phase` should become fields.

---

# 3. Query semantics: K-relations first, FOL second

Generate a deeply embedded, intrinsically typed relational query AST. Its exact details can evolve, but the semantic shape should be:

```lean
def Query.eval
    (q : Query S Params RowData)
    (s : DbState S)
    (p : Params) :
    KRel RowData
```

Define row support as:

```lean
def Query.Holds
    (q : Query S Params RowData)
    (s : DbState S)
    (p : Params)
    (r : RowData) : Prop :=
  0 < (q.eval s p).mult r
```

For the core operators, the denotation follows the standard bag equations:

```text
scan t:
  multiplicity is s.rel t

filter φ q:
  retain q's multiplicity exactly when φ evaluates to SQL true

project f q:
  sum the multiplicities of every source row projected to the output row

join φ q₁ q₂:
  multiply left and right multiplicities for matching pairs

antiJoin φ q₁ q₂:
  retain a left occurrence exactly when no matching right row exists

unionAll:
  add multiplicities

distinct:
  replace each positive multiplicity by one
```

The finite support of the input relations makes the sums and quantification finite.

## 3.1 Typed expressions and SQL truth

The logical kernel should distinguish SQL truth from Lean `Bool` or `Prop`:

```lean
inductive SqlTruth
  | true
  | false
  | unknown

def SqlTruth.wherePasses : SqlTruth → Prop
  | .true    => True
  | .false   => False
  | .unknown => False

def SqlTruth.checkPasses : SqlTruth → Prop
  | .false   => False
  | .true    => True
  | .unknown => True
```

The second coercion is needed because PostgreSQL `CHECK` and query `WHERE` clauses treat unknown differently.

Expressions and predicates should be typed and resolved:

```lean
inductive Expr (S : Schema) (Γ : List Sort) :
    SqlType → Type
  | column
  | param
  | literal
  | call
  | cast
  | ...
```

Operator definitions must be keyed by their resolved PostgreSQL identity, argument types, and collation. SQL equality should be simplified to Lean equality only when the runtime has a theorem-backed mapping. In particular, PostgreSQL nondeterministic collations may consider different strings equal, so Lean `String` equality is not a universally valid model of SQL text equality. ([PostgreSQL][6])

## 3.2 Internal outer-join rows need a presence bit

An internal left-join result should have a shape equivalent to:

```lean
LeftRow × Option RightRow
```

The `none` case represents the null-extension introduced because no right row matched. A `some right` value may itself contain nullable fields.

This distinction must survive until predicates have been analyzed. Otherwise the implementation cannot soundly distinguish:

* no matching right row; from
* a matching right row whose selected fields happen to be null.

The final SQL projection can erase the presence bit by mapping `none` to SQL-null columns.

---

# 4. Three generated query contracts

Every logic-supported query should generate three related propositions.

## 4.1 Local postcondition

```lean
def LocalPred
    (p : Params)
    (r : RowData) : Prop :=
  ...
```

`LocalPred` may mention only:

* result fields;
* query parameters;
* modeled pure constants and functions.

It must be decidable from the returned value. Generate a proof-producing validator following the existing `protovalidate-lean` pattern:

```lean
def checkLocal
    (p : Params)
    (r : RowData) :
    Pg.Decision (LocalPred p r)

def validateLocal
    (p : Params)
    (r : RowData) :
    Except Pg.QueryViolation {x : RowData // LocalPred p x}
```

`protovalidate-lean` already demonstrates the appropriate shape: an evidence-carrying decision procedure, a refinement subtype, and kernel-checked soundness and completeness theorems. ([GitHub][7])

For:

```sql
SELECT p.*
FROM person p
WHERE p.name = 'foo'
```

and a nonnullable, theorem-backed text equality, the local contract is:

```lean
def LocalPred (_ : Params) (p : Person.Data) : Prop :=
  p.name = "foo"
```

This proof can be constructed independently of any database-state model. If PostgreSQL or the query contract produces a row named `"bar"`, decoding succeeds but local validation rejects it.

Local extraction should be conservative and generic. A structurally defined approximation:

```lean
Query.localFormula : Query → Formula
```

should satisfy:

```lean
theorem localFormula_sound :
  q.Holds s p r → q.localFormula.denote p r
```

For conjunctions it can retain state-independent conjuncts. For disjunctions, negations, or hidden projected-away values, it may have to return `True`.

For example:

```sql
SELECT p.id
FROM person p
WHERE p.name = 'foo'
```

has no useful local proposition about `id` alone. Its state-indexed proposition still records the existence of an appropriate `Person`.

## 4.2 State-indexed row postcondition

```lean
def ScopedPred
    (s : AppDb.State)
    (p : Params)
    (r : RowData) : Prop :=
  ...
```

This is the FOL-style support characterization of the query:

```lean
theorem holds_iff_scoped :
  query.Holds s p r ↔ ScopedPred s p r
```

The theorem should be obtained structurally from the query AST, not by invoking an arbitrary FOL solver.

For a projection, the generated predicate will usually introduce existential witnesses:

```lean
ScopedPred s p output :=
  ∃ source : Person.At s,
    source.val.name = "foo" ∧
    output.id = source.val.id
```

For `SELECT p.*`, this simplifies to table membership plus the filter:

```lean
ScopedPred s p person :=
  s.Mem .person person ∧
  person.name = "foo"
```

Generate:

```lean
theorem scoped_implies_local :
  ScopedPred s p r → LocalPred p r
```

when `LocalPred` is not simply `True`.

## 4.3 Exact result postcondition

A sequence of state-indexed row subtypes is not, by itself, a complete query specification. It says every returned row satisfies the predicate, but not:

* that no row is missing;
* that multiplicities are correct;
* that no duplicate was added;
* that the server returned the complete result.

Therefore generate:

```lean
def ResultPred
    (s : AppDb.State)
    (p : Params)
    (rows : Array RowData) : Prop :=
  Pg.Logic.KRel.ofArray rows = query.eval s p
```

The equality is bag equality. Unless the query has a modeled `ORDER BY`, the physical order of `rows` is not part of the proposition.

Package it as:

```lean
structure ResultAt
    (s : AppDb.State)
    (p : Params) where
  rows  : Array RowData
  exact : ResultPred s p rows
```

Then provide a generic derivation:

```lean
def ResultAt.refinedRows
    (result : ResultAt s p) :
    Array {r : RowData // ScopedPred s p r}
```

This is the strongest and most useful quantified result type. It preserves duplicates in the array while giving every occurrence its state-indexed proposition.

Queries involving `ORDER BY` may additionally generate an ordering proposition. `LIMIT` or `OFFSET` should initially require a sufficiently modeled ordering contract; otherwise logic generation should be rejected even though ordinary type generation can proceed.

---

# 5. The anti-join example

Consider:

```sql
SELECT f.*
FROM foo AS f
WHERE NOT EXISTS (
  SELECT 1
  FROM bar AS b
  WHERE b.name = f.name
)
```

The generated proposition should be:

```lean
def ScopedPred
    (s : AppDb.State)
    (_ : Params)
    (f : Foo.Data) : Prop :=
  s.Mem .foo f ∧
  ¬ ∃ b : Bar.At s,
      Pg.SqlTruth.wherePasses
        (Pg.Sql.eq b.val.name f.name)
```

With suitable non-null and operator-semantics hypotheses, generate a simplification theorem:

```lean
theorem scopedPred_eq_noMatchingName
    (hIntegrity : AppDb.IntegrityContext .committed s) :
    ScopedPred s () f ↔
      s.Mem .foo f ∧
      ¬ ∃ b : Bar.At s,
          b.val.name = f.name
```

The unsimplified predicate is the authoritative one. This matters when either name is nullable: SQL equality may be unknown, and an unknown comparison does not make the subquery return a matching row.

A contextual subtype is then exactly:

```lean
abbrev FooWithoutBarAt
    (s : AppDb.State) :=
  { f : Foo.Data // ScopedPred s () f }
```

A consumer can recover the quantified fact directly:

```lean
theorem FooWithoutBarAt.noMatchingBar
    (x : FooWithoutBarAt s) :
    ¬ ∃ b : Bar.At s,
        Pg.SqlTruth.wherePasses
          (Pg.Sql.eq b.val.name x.val.name) :=
  x.property.2
```

The proof remains true forever because it is about the immutable value `s`. It says nothing about a later state `s'`.

## Left-join anti-join idiom

Now consider:

```sql
SELECT f.*
FROM foo AS f
LEFT JOIN bar AS b
  ON b.name = f.name
WHERE b.id IS NULL
```

This must not be normalized unconditionally to `NOT EXISTS`.

If `bar.id` is nullable, a real matching `bar` row with a null `id` causes the predicate to pass. The raw generated semantics should retain the outer-join presence bit.

Only under a state integrity hypothesis such as:

```lean
∀ b : Bar.At s, b.val.id.isSome
```

may codegen expose:

```lean
theorem leftJoinNull_eq_antiJoin
    (h : AppDb.Bar.idNotNull.Holds s) :
    RawScopedPred s f ↔ AntiJoinScopedPred s f
```

This demonstrates why schema constraints should be theorem hypotheses used to simplify exact query semantics rather than assumptions baked into the query translator.

---

# 6. The critical trust boundary

A PostgreSQL response is external data. A nominal snapshot token does not transform that data into a Lean proof.

Suppose the runtime had an unchecked primitive of the conceptual type:

```lean
run :
  SnapshotTx σ →
  IO {rows : Array RowData // ResultPred s p rows}
```

Unless it evaluated `ResultPred` over a concrete Lean state, checked a certificate, or relied on an axiom connecting PostgreSQL to `s`, a buggy or malicious server could cause Lean to construct a proof of an arbitrary false proposition. Scoping such a proof to `σ` does not repair the problem: a false scoped proposition can still imply a scope-independent contradiction.

This is particularly relevant because `pg-lean` currently audits for stray axioms, `unsafe`, foreign externals, and other additions to its trusted surface. The generated logic layer should preserve that posture rather than hide “PostgreSQL is correct” behind an opaque theorem. ([GitHub][8])

The runtime should therefore expose three explicit assurance levels.

## 6.1 Validated live observation

```lean
structure Observation
    (σ : Type)
    (q : QuerySpec db)
    (p : q.Params) where
  rows  : Array (q.LocalRow p)
  trace : QueryTrace
```

Execution returns:

```lean
def QuerySpec.observe
    (q : QuerySpec db)
    (p : q.Params) :
    SnapshotM db σ (Observation σ q p)
```

The rows carry genuine `LocalPred` proofs produced by Lean validation.

`Observation` may define a proposition relating it to a proposed state:

```lean
def Observation.Conforms
    (obs : Observation σ q p)
    (s : DbState db.schema) : Prop :=
  q.ResultPred s p (obs.rows.map Subtype.val)
```

but it carries no proof of `Conforms`.

This type is still useful:

* observations from the same `σ` can be grouped operationally;
* query text and descriptor hashes remain attached;
* a later reification can certify them;
* application specifications may assume `Conforms` explicitly.

## 6.2 Reified-state certification

Provide an opt-in operation that captures the finite relations required by a query into Lean data:

```lean
structure ReifiedSnapshot
    (σ : Type)
    (support : Finset AppDb.Table) where
  state : AppDb.StateView support
  metadata : CaptureMetadata
```

A pure Lean evaluator can then construct:

```lean
def Query.evalCertified
    (snap : ReifiedSnapshot σ q.support)
    (p : q.Params) :
    q.ResultAt snap.state p
```

To certify an observed server result:

```lean
def Query.certifyObservation
    (snap : ReifiedSnapshot σ q.support)
    (obs  : Observation σ q p) :
    Except ResultDifference
      (q.ResultAt snap.state p)
```

The implementation:

1. evaluates the generated query AST over `snap.state`;
2. compares its bag with the observed rows;
3. returns an equality proof when they agree.

The resulting quantified subtype is fully kernel-meaningful relative to `snap.state`.

There remains a separate proposition:

```lean
RepresentsPostgresSnapshot σ snap.state
```

Capturing rows over the PostgreSQL protocol does not by itself prove this proposition. The reified result proves facts about the captured Lean state. Relating that state to the physical PostgreSQL engine still requires a backend assumption, a verified backend, or an authenticated completeness certificate.

This distinction should be visible in the API rather than suppressed.

## 6.3 Explicit abstract-backend law

For application verification, provide a specification interface:

```lean
class BackendConforms
    (backend : Type)
    (db : DatabaseDesc) : Prop where
  query_sound :
    ∀ {σ q p} (obs : Observation σ q p),
      obs.Conforms (snapshotState obs)
```

The assured `pg-lean` core should not contain a concrete instance for an ordinary PostgreSQL connection.

An optional target such as:

```text
//Pg/Assumed:postgres_semantics
```

may introduce the backend law for applications willing to trust PostgreSQL's implementation. The dependency makes the assumption visible to Bazel and to assurance audits.

A verified in-memory backend or future proof-carrying database adapter could provide a theorem-backed instance.

This follows the abstract-data-type refinement pattern used by systems such as Fiat: client programs reason against a declarative relational specification, while correctness of a particular implementation is a distinct refinement obligation. ([MIT CSAIL][9])

---

# 7. Positive evidence, negative evidence, and reification cost

The code generator should analyze each generated support formula and emit an evidence requirement:

```lean
structure EvidenceDemand where
  witnesses      : Finset AppDb.Table
  closedWorld    : Finset AppDb.Table
  multiplicities : Finset AppDb.Table
```

The classifications have different operational meanings.

## Positive occurrence

For:

```lean
∃ p : Person.At s, condition p
```

a particular `Person` row can serve as a witness. Full enumeration of `Person` is not logically necessary for this one proposition.

## Negative occurrence

For:

```lean
¬ ∃ b : Bar.At s, condition b
```

witnesses are insufficient. Certification needs a closed-world interpretation of the relevant `Bar` relation, or another checkable nonmembership certificate.

For the anti-join example:

```lean
witnesses   = { Foo }
closedWorld = { Bar }
```

## Multiplicities

Exact results, aggregates, `EXCEPT ALL`, and other bag-sensitive operations require complete multiplicity information for their source relations.

Initially, model-certified execution should capture every referenced occurrence of each required table. It will be too expensive for many production-size tables, but that cost reflects the strength of the requested proposition: proving absence or complete query output requires completeness evidence somewhere.

Later optimizations may use:

* query-specific relation slices with separately proved completeness;
* authenticated indexes or Merkle nonmembership proofs;
* a trusted PostgreSQL extension producing checkable certificates;
* verified materialized snapshots;
* provenance witnesses for positive subformulas.

Ordinary PostgreSQL indexes are performance structures, not proof certificates, so their presence alone should not change the logical evidence requirement.

---

# 8. Separate logical state from runtime snapshot scope

Use different symbols and types deliberately:

```text
s : AppDb.State   -- semantic interpretation of table relations
σ : Type          -- nominal runtime snapshot scope
```

A type index `σ` cannot replace `s`. It contains no relation interpretation. Conversely, `s` alone does not establish that two live queries observed the same PostgreSQL snapshot.

## 8.1 Snapshot-indexed effect

A suitable runtime shape is:

```lean
opaque SnapshotM
    (db : DatabaseDesc)
    (σ : Type)
    (α : Type) : Type

def withReadOnlySnapshot
    (conn : CheckedConnection db)
    (k : (σ : Type) → SnapshotM db σ α) :
    IO (Except Pg.Error α)
```

Only `withReadOnlySnapshot` runs `SnapshotM`. Query operations inside it all use the same `σ`.

This is analogous to Lean's `ST` state-thread parameter: a universally scoped type parameter prevents ordinary values tagged with one state thread from being confused with another. ([Lean Language][10])

Because Lean is not linear, the implementation should also retain a runtime open/closed state. The type index provides nominal separation; the runtime state machine provides resource-lifetime enforcement.

## 8.2 Mapping to PostgreSQL isolation

At Read Committed, each ordinary `SELECT` receives a statement-start snapshot, and two successive statements may see different data. Therefore a Read Committed API should create a fresh `σ` for each statement. ([PostgreSQL][11])

A read-only Repeatable Read transaction is the natural default when several generated queries must share a logical snapshot: successive reads see the same pre-existing database state. A read-write Repeatable Read transaction still sees its own writes, so its logical state evolves and must be modeled as `s₀`, `s₁`, and so forth rather than one immutable `s`. ([PostgreSQL][11])

Serializable transactions provide the appropriate eventual abstraction for state-transition proofs, but results that depend on serializability should generally be published only after successful commit. PostgreSQL may abort such transactions and require a complete retry; a serializable read-only deferrable transaction is the special case in which PostgreSQL waits for a safe snapshot before returning data. ([PostgreSQL][11])

For parallel state capture, PostgreSQL can export one transaction's snapshot and import it into other sessions while the exporting transaction remains open. This is suitable for a future parallel reifier. ([PostgreSQL][12])

---

# 9. Codegen architecture

The existing server-authoritative codegen decision remains correct, but `Parse` and `Describe` alone are not enough to construct logical semantics. They expose parameter and result types, not the resolved relational structure of the query.

## 9.1 Obtain a resolved query tree from PostgreSQL

Add a codegen-only PostgreSQL extension for each supported major version:

```text
pg_lean_analyze_pg17
pg_lean_analyze_pg18
```

It should run after parse analysis and rewriting but before planning, and serialize a stable canonical representation of:

* range-table entries and relation identities;
* resolved columns;
* join kinds and join predicates;
* target expressions;
* parameter positions and types;
* operator and function identities;
* casts and collations;
* `EXISTS`, `NOT EXISTS`, and correlated references;
* nonrecursive CTEs;
* sort, distinct, grouping, limit, and other semantic nodes.

Use the analyzed tree rather than an `EXPLAIN` plan. Plans are optimizer artifacts and may replace, reorder, or erase source-level semantic constructs. A post-analysis tree retains resolved name and operator information without tying generated logic to a particular optimizer decision.

The extension is intentionally version-specific because PostgreSQL's internal analyzed-tree structures are not a stable public interchange format. Each adapter emits the same versioned `AnalyzerIR`.

The existing protocol-level `Parse` and `Describe` result should still be used to cross-check final parameter and output contracts.

## 9.2 Lower into a small typed relational IR

The Lean code generator consumes `AnalyzerIR` and lowers it into:

```lean
Pg.Logic.Query
Pg.Logic.Expr
Pg.Logic.SqlTruth
```

All semantic normalization after this boundary should occur in Lean code with generic theorems.

For example:

```text
AnalyzerIR NOT EXISTS
    ↓
Query.antiJoin
    ↓
KRel denotation
    ↓
state-indexed Formula
    ↓
ScopedPred
```

The PostgreSQL-to-`AnalyzerIR` serializer remains part of the codegen trust boundary. Keep it small, perform no semantic optimization in it, retain the source SQL and IR in the generated snapshot, and test it differentially against PostgreSQL on generated finite databases.

## 9.3 Derive logic metadata structurally

From the typed query AST, the Lean generator computes:

```lean
query.support
query.formula
query.localFormula
query.evidenceDemand
query.constraintDependencies
query.logicStatus
```

Generic kernel-checked theorems should establish:

```lean
query.formula_correct
query.localFormula_sound
query.evidenceDemand_sound
query.exact_implies_scoped
query.scoped_implies_local
```

The generated per-query module mostly supplies constants and readable aliases rather than custom proof scripts.

## 9.4 Supported logical fragment

The first logical milestone should include:

* base-table scans;
* filters;
* projections;
* inner and cross joins;
* left joins;
* semijoins and antijoins;
* `EXISTS` and `NOT EXISTS`;
* null tests and Boolean combinations;
* supported scalar comparisons;
* `UNION ALL`;
* `DISTINCT`;
* nonrecursive CTE expansion.

Type generation may continue to support more PostgreSQL queries. Logical generation should report one of:

```lean
inductive LogicStatus
  | exact
  | localOnly
  | typedOnly (reason : String)
```

A query manifest option:

```json
{ "logic": "required" }
```

should turn `localOnly` or `typedOnly` into a build failure.

Initially reject or downgrade logic for:

* recursive CTEs;
* window functions;
* unmodeled aggregates;
* nondeterministic `LIMIT`/`OFFSET`;
* volatile functions;
* unsupported collations or operators;
* row-level security or role-dependent policies not included in the semantic context;
* procedural or extension functions without a Lean semantics plugin.

Full PostgreSQL is not first-order. Aggregation needs multiplicity arithmetic, recursive CTEs need fixed-point semantics, and ordering introduces sequence semantics. The K-relational query AST permits those extensions later without pretending they already belong to the FOL fragment.

---

# 10. Generated module shape

For the anti-join example:

```text
AppDb/
  Logic/
    Schema.lean
    State.lean
    Integrity.lean

  Queries/
    FooWithoutBar/
      Types.lean
      Rel.lean
      Predicates.lean
      Runtime.lean
```

The generated declarations should resemble:

```lean
namespace AppDb.Queries.FooWithoutBar

structure Params where

abbrev RowData := AppDb.Foo.Data

def rel :
    Pg.Logic.Query
      AppDb.schema
      Params
      RowData :=
  ...

def LocalPred
    (_ : Params)
    (_ : RowData) : Prop :=
  True

def ScopedPred
    (s : AppDb.State)
    (_ : Params)
    (f : RowData) : Prop :=
  s.Mem .foo f ∧
  ¬ ∃ b : AppDb.Bar.At s,
      Pg.SqlTruth.wherePasses
        (Pg.Sql.eq b.val.name f.name)

def ResultPred
    (s : AppDb.State)
    (p : Params)
    (rows : Array RowData) : Prop :=
  Pg.Logic.KRel.ofArray rows = rel.eval s p

abbrev LocalRow (p : Params) :=
  {r : RowData // LocalPred p r}

abbrev RowAt
    (s : AppDb.State)
    (p : Params) :=
  {r : RowData // ScopedPred s p r}

abbrev ResultAt
    (s : AppDb.State)
    (p : Params) :=
  Pg.Logic.ResultAt rel s p

theorem holds_iff_scoped :
    rel.Holds s p r ↔ ScopedPred s p r :=
  ...

theorem scoped_implies_local :
    ScopedPred s p r → LocalPred p r :=
  ...

def observe
    (p : Params) :
    Pg.Typed.SnapshotM AppDb.database σ
      (Pg.Typed.Observation σ spec p) :=
  ...

def certify
    (snap : Pg.Typed.ReifiedSnapshot σ rel.support)
    (obs  : Pg.Typed.Observation σ spec p) :
    Except Pg.Typed.ResultDifference
      (ResultAt snap.state p) :=
  ...

end AppDb.Queries.FooWithoutBar
```

---

# 11. Schema constraints and query propositions share one logic

The same typed expression and formula language should represent:

* query filters;
* check constraints;
* domain constraints;
* not-null guarantees;
* foreign keys;
* uniqueness and exclusion constraints;
* generated-column relationships.

Examples:

```lean
def PersonCheck.Holds (s : State) : Prop :=
  ∀ p : Person.At s,
    SqlTruth.checkPasses (personCheckExpr p.val)

def ChildForeignKey.Holds (s : State) : Prop :=
  ∀ c : Child.At s,
    keyIsNull c.val ∨
    ∃ p : Parent.At s,
      keysMatch c.val p.val

def UniqueEmail.Holds (s : State) : Prop :=
  ∀ x y : Person.OccAt s,
    sqlUniqueKeysEqual x.1 y.1 →
    x = y
```

Using `OccAt` in uniqueness propositions correctly detects two physically distinct occurrences having identical field values.

Query simplification should always make its assumptions explicit:

```lean
theorem queryPredicate_simplified
    (h₁ : BarIdNotNull.Holds s)
    (h₂ : NameEqualityModeled s) :
    RawScopedPred s p r ↔ SimplifiedScopedPred s p r
```

This gives a direct route from PostgreSQL catalog constraints to Lean propositions without conflating state invariants with row carrier types.

---

# 12. Transaction and program logic

Once individual query semantics exists, generated database operations can receive state-transition specifications.

A minimal specification type is:

```lean
structure DbSpec
    (S : Schema)
    (α : Type) where
  pre  : DbState S → Prop
  post : DbState S → α → DbState S → Prop
```

For a read query:

```lean
def readSpec (q : Query S P R) (p : P) :
    DbSpec S (Array R) where
  pre  := fun _ => True
  post := fun s rows s' =>
    s' = s ∧ q.ResultPred s p rows
```

For an insert, update, or delete, `post` describes the corresponding bag transformation and the applicable constraint phase.

The predicate-transformer form is:

```lean
abbrev DbWP
    (S : Schema)
    (α : Type) :=
  (α → DbState S → Prop) →
  DbState S →
  Prop
```

A later `WP` instance can integrate these operations with Lean's `mvcgen`. Serializable execution then becomes an implementation/refinement theorem relating the live transaction runner to the abstract state-transition program.

Isolation logics based on separation logic are relevant if the project eventually verifies a transaction runtime or weak-isolation implementation itself. Recent Iris work has mechanized modular specifications for read-uncommitted, read-committed, and snapshot isolation, demonstrating that this is feasible, but it is substantially heavier than the state-indexed read-query layer needed initially. ([arXiv][13])

---

# 13. Implementation sequence

## Milestone 1: logical kernel

Implement:

```text
Pg/Logic/KRel.lean
Pg/Logic/Schema.lean
Pg/Logic/SqlTruth.lean
Pg/Logic/Expr.lean
Pg/Logic/Formula.lean
Pg/Logic/Query.lean
Pg/Logic/Result.lean
```

Support scans, filters, projections, inner joins, left joins, `EXISTS`, and `NOT EXISTS`. Establish generic evaluation, support-formula, and exact-result theorems.

## Milestone 2: analyzed query IR

Implement the PostgreSQL 17 and 18 analyzer serializers and:

```text
Pg/Codegen/AnalyzerIR.lean
Pg/Codegen/LowerQuery.lean
Pg/Codegen/EmitLogic.lean
```

Cross-check `AnalyzerIR` parameters and outputs against `Parse` and `Describe`.

## Milestone 3: generated local and scoped contracts

Generate:

* `LocalPred`;
* `ScopedPred`;
* `ResultPred`;
* local proof-producing validators;
* `holds_iff_scoped`;
* `scoped_implies_local`;
* evidence-demand metadata.

At this point ordinary live queries can safely return local refinement subtypes.

## Milestone 4: snapshot-scoped observations

Implement:

```text
Pg/Typed/SnapshotM.lean
Pg/Typed/Observation.lean
```

Provide statement-scoped Read Committed execution and read-only Repeatable Read scopes. Add exported-snapshot support later.

## Milestone 5: reified certification

Implement:

```text
Pg/Typed/ReifiedSnapshot.lean
Pg/Typed/Certify.lean
```

Capture query support relations, evaluate generated query semantics in Lean, compare result bags, and return `ResultAt`.

The first acceptance test should be the anti-join example, including duplicate rows and nullable join keys.

## Milestone 6: state integrity and transactions

Generate supported schema constraints as `State → Prop`, including catalog phase information. Add the `DbSpec` or `DbWP` layer for DML and transaction verification.

---

# Locked invariants

The implementation should preserve these invariants:

1. A generated record type is a carrier of possible values, never the extension of a table.
2. A table at a snapshot is a finite bag interpretation inside `DbState`.
3. `RowAt s t` and `OccAt s t` are derived state-indexed types; the latter is used where duplicates matter.
4. K-relational semantics is authoritative; FOL propositions characterize support where the query fragment permits it.
5. Query contracts are split into local, state-indexed, and exact-bag levels.
6. A live PostgreSQL response can construct local proofs, but not quantified state proofs without reification, a certificate, or an explicit backend law.
7. The nominal runtime index `σ` and the semantic state value `s` solve different problems and are never conflated.
8. Negative predicates require closed-world evidence over the negatively referenced relation.
9. Schema constraints are explicit predicates on states and are used only under their validation, enforcement, and transaction-phase hypotheses.
10. Query logic is derived from PostgreSQL's analyzed tree, not from planner output or syntactic heuristics.
11. Unsupported SQL remains type-checkable where possible, but never receives an approximated logical guarantee.
12. Arbitrary SQL theorem proving is not a codegen requirement; the generator derives exact semantics structurally and performs only theorem-backed simplifications.

The decisive conceptual move is therefore not to make `Person` itself a state-indexed record. It is to make the generated schema a signature, each snapshot a finite model of that signature, and `Person.At s` a dependent subtype derived from the model's relation interpretation. That gives quantified query results a precise context, preserves PostgreSQL bag semantics, and keeps the boundary between external observations and Lean proofs explicit.

[1]: https://homepages.inf.ed.ac.uk/libkin/papers/pvldb17.pdf "https://homepages.inf.ed.ac.uk/libkin/papers/pvldb17.pdf"
[2]: https://arxiv.org/pdf/1610.02101 "https://arxiv.org/pdf/1610.02101"
[3]: https://arxiv.org/abs/1701.05699 "https://arxiv.org/abs/1701.05699"
[4]: https://arxiv.org/abs/1608.06499 "https://arxiv.org/abs/1608.06499"
[5]: https://www.postgresql.org/docs/current/catalog-pg-constraint.html "https://www.postgresql.org/docs/current/catalog-pg-constraint.html"
[6]: https://www.postgresql.org/docs/current/collation.html?utm_source=chatgpt.com "Documentation: 18: 23.2. Collation Support"
[7]: https://github.com/pb64-lean/protovalidate-lean "https://github.com/pb64-lean/protovalidate-lean"
[8]: https://github.com/pb64-lean/pg-lean "https://github.com/pb64-lean/pg-lean"
[9]: https://people.csail.mit.edu/jgross/personal-website/papers/2015-adt-synthesis.pdf "https://people.csail.mit.edu/jgross/personal-website/papers/2015-adt-synthesis.pdf"
[10]: https://lean-lang.org/doc/reference/latest/IO/Mutable-References/ "https://lean-lang.org/doc/reference/latest/IO/Mutable-References/"
[11]: https://www.postgresql.org/docs/current/transaction-iso.html "https://www.postgresql.org/docs/current/transaction-iso.html"
[12]: https://www.postgresql.org/docs/current/functions-admin.html "https://www.postgresql.org/docs/current/functions-admin.html"
[13]: https://arxiv.org/abs/2501.14421 "https://arxiv.org/abs/2501.14421"


====
