module

public import Pgx.Logic.State
public import Pgx.Constraint.IR

public section

/-!
# Relational PostgreSQL constraint semantics

These predicates describe constraints over the logical occurrences in a
finite database state.  They deliberately receive key projections and
PostgreSQL-aware comparison operations from their caller.  In particular,
none of the definitions below substitutes Lean row equality for an SQL
operator, collation, or null policy.

The definitions are propositions over an arbitrary `State`; they do not claim
that a live external database is represented by that state.
-/

namespace Pgx.Logic.Constraint

abbrev SqlTruth := Pgx.Constraint.SqlTruth

/-- PostgreSQL's two unique-key null policies. -/
inductive UniqueNulls where
  /-- Ordinary unique constraints: a null in a key prevents a conflict. -/
  | distinct
  /-- `NULLS NOT DISTINCT`: corresponding nulls compare as one key value. -/
  | notDistinct
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Comparisons required to interpret a UNIQUE key.

`equal` is the resolved compound SQL equality and may return `unknown`.
`notDistinct` is supplied separately because ordinary SQL equality cannot
distinguish two nulls from one null; it must implement the constraint's
two-valued `IS NOT DISTINCT FROM`-style key comparison. -/
structure UniqueComparator (Key : Type u) where
  equal : Key → Key → SqlTruth
  notDistinct : Key → Key → Bool

namespace UniqueComparator

/-- Whether two projected keys conflict under the selected null policy. -/
def conflicts (comparator : UniqueComparator Key) (nulls : UniqueNulls)
    (left right : Key) : Bool :=
  match nulls with
  | .distinct => comparator.equal left right == .true
  | .notDistinct => comparator.notDistinct left right

end UniqueComparator

/-- Two state occurrences are distinct independently of their row values.
This remains meaningful when the same complete row value occurs twice. -/
def DistinctOccurrences (left right : OccAt state table) : Prop :=
  left.index ≠ right.index

/-- A UNIQUE constraint: no two distinct occurrences have conflicting keys.

The projector is explicit so generated code can select exactly the constrained
columns, and the comparator is explicit so operator/collation/null semantics
never come from Lean equality accidentally. -/
def Unique (state : State schema) (table : schema.Table)
    (key : schema.Row table → Key) (comparator : UniqueComparator Key)
    (nulls : UniqueNulls) : Prop :=
  ∀ left right : OccAt state table,
    DistinctOccurrences left right →
      comparator.conflicts nulls (key left.row) (key right.row) = false

/-- Comparisons and null recognition required by a primary key. -/
structure PrimaryKeyComparator (Key : Type u) where
  /-- True exactly when every component of the compound key is non-null. -/
  allNotNull : Key → Bool
  /-- Resolved compound equality for non-null keys. -/
  equal : Key → Key → SqlTruth

namespace PrimaryKeyComparator

def conflicts (comparator : PrimaryKeyComparator Key) (left right : Key) : Bool :=
  comparator.equal left right == .true

end PrimaryKeyComparator

/-- A primary key combines per-occurrence non-nullness with uniqueness. -/
def PrimaryKey (state : State schema) (table : schema.Table)
    (key : schema.Row table → Key) (comparator : PrimaryKeyComparator Key) : Prop :=
  (∀ occurrence : OccAt state table,
      comparator.allNotNull (key occurrence.row) = true) ∧
  (∀ left right : OccAt state table,
      DistinctOccurrences left right →
        comparator.conflicts (key left.row) (key right.row) = false)

/-- Null distribution in a possibly compound foreign key. -/
inductive NullShape where
  | noNulls
  | partialNulls
  | allNulls
  deriving Repr, BEq, DecidableEq, Inhabited

/-- PostgreSQL foreign-key match modes supported by this kernel.
`MATCH PARTIAL` is intentionally absent until a PostgreSQL version adapter
provides and validates its exact semantics. -/
inductive ForeignKeyMatch where
  | simple
  | full
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Key operations for a foreign key.  Referencing and referenced key carrier
types may differ because PostgreSQL can resolve a cross-type comparison. -/
structure ForeignKeyComparator (ChildKey : Type u) (ParentKey : Type v) where
  nullShape : ChildKey → NullShape
  compare : ChildKey → ParentKey → SqlTruth

namespace ForeignKeyComparator

/-- Whether one referenced key is a successful SQL foreign-key match.  Only
SQL true is a match; false and unknown do not witness referential integrity. -/
def isMatch (comparator : ForeignKeyComparator ChildKey ParentKey)
    (child : ChildKey) (parent : ParentKey) : Bool :=
  comparator.compare child parent == .true

end ForeignKeyComparator

/-- The obligation contributed by one referencing occurrence. -/
def ForeignKeyOccurrence
    (state : State schema) (parentTable : schema.Table)
    (mode : ForeignKeyMatch) (child : ChildKey)
    (parentKey : schema.Row parentTable → ParentKey)
    (comparator : ForeignKeyComparator ChildKey ParentKey) : Prop :=
  match mode, comparator.nullShape child with
  | .simple, .partialNulls | .simple, .allNulls => True
  | .full, .allNulls => True
  | .full, .partialNulls => False
  | .simple, .noNulls | .full, .noNulls =>
      ∃ parent : OccAt state parentTable,
        comparator.isMatch child (parentKey parent.row) = true

/-- A foreign key over all referencing occurrences.

Under `MATCH SIMPLE`, any null component exempts the referencing occurrence.
Under `MATCH FULL`, all components may be null, but a partially-null key is a
violation.  A non-null key in either mode requires an actual parent occurrence
whose supplied PostgreSQL comparison evaluates to true. -/
def ForeignKey
    (state : State schema) (childTable parentTable : schema.Table)
    (mode : ForeignKeyMatch)
    (childKey : schema.Row childTable → ChildKey)
    (parentKey : schema.Row parentTable → ParentKey)
    (comparator : ForeignKeyComparator ChildKey ParentKey) : Prop :=
  ∀ child : OccAt state childTable,
    ForeignKeyOccurrence state parentTable mode (childKey child.row)
      parentKey comparator

/-- Comparisons for one exclusion key.  Each array element is the result of
one resolved exclusion operator.  PostgreSQL reports a conflict only when
every operator comparison is SQL true. -/
structure ExclusionComparator (Key : Type u) where
  compare : Key → Key → Array SqlTruth

namespace ExclusionComparator

def conflicts (comparator : ExclusionComparator Key) (left right : Key) : Bool :=
  (comparator.compare left right).all (fun result => result == .true)

end ExclusionComparator

/-- An exclusion constraint over distinct row occurrences.

An SQL false *or unknown* result from any supplied exclusion operator prevents
a conflict, matching PostgreSQL's exclusion semantics.  The empty comparison
array conflicts vacuously; code generation should reject such malformed
constraint metadata before constructing this predicate. -/
def Exclusion (state : State schema) (table : schema.Table)
    (key : schema.Row table → Key) (comparator : ExclusionComparator Key) : Prop :=
  ∀ left right : OccAt state table,
    DistinctOccurrences left right →
      comparator.conflicts (key left.row) (key right.row) = false

end Pgx.Logic.Constraint
