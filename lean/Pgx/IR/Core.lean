/-!
# Symbolic PostgreSQL IR primitives

These declarations are the dependency foundation shared by the canonical
database IR and the typed local-constraint IR.  They contain no physical
catalog identifiers: installation-local OIDs are deliberately excluded.
-/

namespace Pgx

inductive TypeKind where
  | base
  | enum
  | domain
  | array
  | range
  | multirange
  | composite
  | pseudo
  deriving Repr, BEq, DecidableEq, Inhabited

namespace TypeKind

def tag : TypeKind → String
  | .base => "base"
  | .enum => "enum"
  | .domain => "domain"
  | .array => "array"
  | .range => "range"
  | .multirange => "multirange"
  | .composite => "composite"
  | .pseudo => "pseudo"

end TypeKind

/-- Stable PostgreSQL type identity. OIDs are intentionally absent. -/
structure TypeKey where
  schema : String
  name : String
  kind : TypeKind
  deriving Repr, BEq, DecidableEq, Inhabited

namespace TypeKey

def display (key : TypeKey) : String := s!"{key.schema}.{key.name} ({key.kind.tag})"

end TypeKey

instance : ToString TypeKey := ⟨TypeKey.display⟩

structure TypeRef where
  key : TypeKey
  typmod : Option Int32 := none
  deriving Repr, BEq, DecidableEq, Inhabited

structure RelationKey where
  schema : String
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

namespace RelationKey

def display (key : RelationKey) : String := s!"{key.schema}.{key.name}"

end RelationKey

instance : ToString RelationKey := ⟨RelationKey.display⟩

structure ColumnKey where
  relation : RelationKey
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure CollationKey where
  schema : String
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Stable identity of a PostgreSQL operator overload.  Operator OIDs are
installation-local; the operand type vector is what disambiguates overloads. -/
structure OperatorKey where
  schema : String
  name : String
  leftType : TypeKey
  rightType : TypeKey
  deriving Repr, BEq, DecidableEq, Inhabited

namespace OperatorKey

def display (key : OperatorKey) : String :=
  s!"{key.schema}.{key.name}({key.leftType.display}, {key.rightType.display})"

end OperatorKey

instance : ToString OperatorKey := ⟨OperatorKey.display⟩

/-- A constraint name is unique only within its owning relation. -/
structure ConstraintKey where
  relation : RelationKey
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ConstraintKey

def display (key : ConstraintKey) : String :=
  s!"{key.relation.display}.{key.name}"

end ConstraintKey

instance : ToString ConstraintKey := ⟨ConstraintKey.display⟩

/-- Stable identity of an index.  PostgreSQL indexes share their schema's
relation namespace, so schema and name are sufficient. -/
structure IndexKey where
  schema : String
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

namespace IndexKey

def display (key : IndexKey) : String := s!"{key.schema}.{key.name}"

end IndexKey

instance : ToString IndexKey := ⟨IndexKey.display⟩

end Pgx
