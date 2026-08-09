import Pg.Crypto.Sha256
import Pg.Crypto.Hex

/-!
# Canonical PostgreSQL schema and query IR

The generator converts installation-local catalog identifiers into this
symbolic representation before any source is emitted.  In particular, OIDs
do not occur in the structures below.
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

/-- Stable PostgreSQL type identity.  OIDs are intentionally absent. -/
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

structure SchemaIR where
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure EnumIR where
  key : TypeKey
  labels : Array String
  deriving Repr, BEq, Inhabited

/-- A domain is branded in Milestone 1; its check expressions remain SQL text
until the local-refinement milestone translates them into propositions. -/
structure DomainIR where
  key : TypeKey
  base : TypeRef
  notNull : Bool
  defaultExpr : Option String := none
  constraints : Array String := #[]
  deriving Repr, BEq, Inhabited

inductive RelationKind where
  | table
  | partitionedTable
  | view
  | materializedView
  | foreignTable
  deriving Repr, BEq, DecidableEq, Inhabited

namespace RelationKind

def tag : RelationKind → String
  | .table => "table"
  | .partitionedTable => "partitioned-table"
  | .view => "view"
  | .materializedView => "materialized-view"
  | .foreignTable => "foreign-table"

end RelationKind

structure RelationColumnIR where
  name : String
  ordinal : Nat
  ty : TypeRef
  nullable : Bool
  identity : Bool := false
  generated : Bool := false
  defaultExpr : Option String := none
  collation : Option CollationKey := none
  deriving Repr, BEq, Inhabited

structure RelationIR where
  key : RelationKey
  kind : RelationKind
  columns : Array RelationColumnIR
  deriving Repr, BEq, Inhabited

inductive ConstraintKind where
  | check
  | notNull
  | primaryKey
  | unique
  | foreignKey
  | exclusion
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ConstraintKind

def tag : ConstraintKind → String
  | .check => "check"
  | .notNull => "not-null"
  | .primaryKey => "primary-key"
  | .unique => "unique"
  | .foreignKey => "foreign-key"
  | .exclusion => "exclusion"

end ConstraintKind

structure ConstraintIR where
  relation : RelationKey
  name : String
  kind : ConstraintKind
  columns : Array String := #[]
  referencedRelation : Option RelationKey := none
  referencedColumns : Array String := #[]
  expression : Option String := none
  validated : Bool := true
  deriving Repr, BEq, Inhabited

structure IndexIR where
  relation : RelationKey
  name : String
  unique : Bool
  primary : Bool
  valid : Bool
  columns : Array String := #[]
  predicate : Option String := none
  expression : Option String := none
  deriving Repr, BEq, Inhabited

inductive Cardinality where
  | execute
  | exactlyOne
  | zeroOrOne
  | many
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Cardinality

def tag : Cardinality → String
  | .execute => "execute"
  | .exactlyOne => "exactlyOne"
  | .zeroOrOne => "zeroOrOne"
  | .many => "many"

end Cardinality

structure ParamIR where
  position : Nat
  name : String
  ty : TypeRef
  nullable : Bool
  deriving Repr, BEq, Inhabited

structure QueryColumnIR where
  name : String
  ty : TypeRef
  nullable : Bool
  origin : Option ColumnKey := none
  collation : Option CollationKey := none
  deriving Repr, BEq, Inhabited

structure QueryIR where
  name : String
  sql : String
  sqlHash : String
  params : Array ParamIR
  columns : Array QueryColumnIR
  cardinality : Cardinality
  deriving Repr, BEq, Inhabited

structure SessionContract where
  searchPath : Array String
  timezone : String := "UTC"
  encoding : String := "UTF8"
  standardConformingStrings : Bool := true
  deriving Repr, BEq, Inhabited

/-- Escape hatch for an extension/user type.  `codec` names a Lean declaration
of type `Pg.Typed.ResolvedCodec leanType`; the Bazel target containing it is a
normal dependency of the generated library. -/
structure TypeOverrideIR where
  key : TypeKey
  leanType : String
  codec : String
  deriving Repr, BEq, Inhabited

structure DatabaseIR where
  formatVersion : Nat := 1
  serverMajor : Nat
  serverFeatures : Array String := #[]
  session : SessionContract
  schemas : Array SchemaIR
  enums : Array EnumIR
  domains : Array DomainIR
  relations : Array RelationIR
  constraints : Array ConstraintIR
  indexes : Array IndexIR
  queries : Array QueryIR
  requiredExtensions : Array (String × String) := #[]
  typeOverrides : Array TypeOverrideIR := #[]
  deriving Repr, BEq, Inhabited

/-! ## Deterministic semantic fingerprint -/

private def atom (value : String) : String :=
  s!"{value.utf8ByteSize}:{value}"

private def boolAtom (value : Bool) : String := if value then "1" else "0"

private def optionAtom (f : α → String) : Option α → String
  | none => "-"
  | some value => "+" ++ f value

private def arrayAtom (f : α → String) (values : Array α) : String :=
  "[" ++ String.join (values.toList.map (fun value => atom (f value))) ++ "]"

private def typeKeyAtom (key : TypeKey) : String :=
  atom key.schema ++ atom key.name ++ atom key.kind.tag

private def typeRefAtom (ref : TypeRef) : String :=
  typeKeyAtom ref.key ++ optionAtom (fun value => toString value) ref.typmod

private def relationKeyAtom (key : RelationKey) : String :=
  atom key.schema ++ atom key.name

private def relationColumnAtom (column : RelationColumnIR) : String :=
  atom column.name ++ atom (toString column.ordinal) ++ typeRefAtom column.ty ++
    boolAtom column.nullable ++ boolAtom column.identity ++ boolAtom column.generated ++
    optionAtom atom column.defaultExpr ++ optionAtom (fun key =>
      atom key.schema ++ atom key.name) column.collation

private def relationAtom (relation : RelationIR) : String :=
  relationKeyAtom relation.key ++ atom relation.kind.tag ++
    arrayAtom relationColumnAtom relation.columns

private def enumAtom (value : EnumIR) : String :=
  typeKeyAtom value.key ++ arrayAtom id value.labels

private def domainAtom (value : DomainIR) : String :=
  typeKeyAtom value.key ++ typeRefAtom value.base ++ boolAtom value.notNull ++
    optionAtom atom value.defaultExpr ++ arrayAtom id value.constraints

private def constraintAtom (value : ConstraintIR) : String :=
  relationKeyAtom value.relation ++ atom value.name ++ atom value.kind.tag ++
    arrayAtom id value.columns ++ optionAtom relationKeyAtom value.referencedRelation ++
    arrayAtom id value.referencedColumns ++ optionAtom atom value.expression ++
    boolAtom value.validated

private def indexAtom (value : IndexIR) : String :=
  relationKeyAtom value.relation ++ atom value.name ++ boolAtom value.unique ++
    boolAtom value.primary ++ boolAtom value.valid ++ arrayAtom id value.columns ++
    optionAtom atom value.predicate ++ optionAtom atom value.expression

private def overrideAtom (value : TypeOverrideIR) : String :=
  typeKeyAtom value.key ++ atom value.leanType ++ atom value.codec

private def queryColumnAtom (column : QueryColumnIR) : String :=
  atom column.name ++ typeRefAtom column.ty ++ boolAtom column.nullable ++
    optionAtom (fun origin => relationKeyAtom origin.relation ++ atom origin.name) column.origin

private def paramAtom (param : ParamIR) : String :=
  atom (toString param.position) ++ atom param.name ++ typeRefAtom param.ty ++
    boolAtom param.nullable

private def queryAtom (query : QueryIR) : String :=
  atom query.name ++ atom query.sqlHash ++ arrayAtom paramAtom query.params ++
    arrayAtom queryColumnAtom query.columns ++ atom query.cardinality.tag

/-- Canonical material for the type-relevant contract.  Physical OIDs, ACLs,
owners, and performance-only index details cannot influence it. -/
def DatabaseIR.contractMaterial (db : DatabaseIR) : String :=
  atom (toString db.formatVersion) ++ atom (toString db.serverMajor) ++
    arrayAtom id db.serverFeatures ++ arrayAtom id db.session.searchPath ++ atom db.session.timezone ++
    atom db.session.encoding ++ boolAtom db.session.standardConformingStrings ++
    arrayAtom enumAtom db.enums ++ arrayAtom domainAtom db.domains ++
    arrayAtom relationAtom db.relations ++ arrayAtom constraintAtom db.constraints ++
    arrayAtom indexAtom (db.indexes.filter fun value => value.unique || value.primary) ++
    arrayAtom queryAtom db.queries ++ arrayAtom (fun value =>
      atom value.1 ++ atom value.2) db.requiredExtensions ++
    arrayAtom overrideAtom db.typeOverrides

def DatabaseIR.contractHashBytes (db : DatabaseIR) : ByteArray :=
  Pg.Crypto.sha256 db.contractMaterial.toUTF8

def DatabaseIR.contractHash (db : DatabaseIR) : String :=
  Pg.Crypto.toHexLower db.contractHashBytes

end Pgx
