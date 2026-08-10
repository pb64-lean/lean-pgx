module

public import Pgx.IR.Core
public import Pgx.Constraint.IR
public import Pg.Crypto.Sha256
public import Pg.Crypto.Hex

public section

/-!
# Canonical PostgreSQL schema and query IR

The generator converts installation-local catalog identifiers into this
symbolic representation before any source is emitted.  In particular, OIDs
do not occur in the structures below.
-/

namespace Pgx

structure SchemaIR where
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure EnumIR where
  key : TypeKey
  labels : Array String
  deriving Repr, BEq, Inhabited

/-- A physical PostgreSQL array type and the symbolic type of each element.
Only the ordinary comma-delimited, one-dimensional value surface is emitted;
the delimiter is nevertheless retained so unsupported extension array shapes
cannot be mistaken for ordinary arrays. -/
structure ArrayIR where
  key : TypeKey
  element : TypeRef
  delimiter : String := ","
  deriving Repr, BEq, Inhabited

structure CompositeFieldIR where
  name : String
  ordinal : Nat
  ty : TypeRef
  collation : Option CollationKey := none
  deriving Repr, BEq, Inhabited

/-- Named composite metadata.  Fields are deliberately not marked NOT NULL:
PostgreSQL table constraints do not constrain values of the table's row type
when that composite is used outside the table. -/
structure CompositeIR where
  key : TypeKey
  fields : Array CompositeFieldIR
  deriving Repr, BEq, Inhabited

structure RoutineKey where
  schema : String
  name : String
  /-- PostgreSQL's input argument vector is the overload identity. -/
  inputTypes : Array TypeRef := #[]
  deriving Repr, BEq, DecidableEq, Inhabited

namespace RoutineKey

def display (key : RoutineKey) : String :=
  let args := String.intercalate ", "
    (key.inputTypes.toList.map (fun ty => ty.key.display))
  s!"{key.schema}.{key.name}({args})"

end RoutineKey

instance : ToString RoutineKey := ⟨RoutineKey.display⟩

structure QualifiedName where
  schema : String
  name : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure RangeIR where
  key : TypeKey
  subtype : TypeRef
  multirange : TypeKey
  collation : Option CollationKey := none
  subtypeOpclass : QualifiedName
  canonical : Option RoutineKey := none
  subtypeDiff : Option RoutineKey := none
  deriving Repr, BEq, Inhabited

structure MultirangeIR where
  key : TypeKey
  range : TypeKey
  deriving Repr, BEq, Inhabited

/-- One locally recheckable domain constraint.  The normalized PostgreSQL
source is retained for diagnostics; `expression` is the typed, authoritative
form used to emit a proposition and its proof-producing validator. -/
structure DomainConstraintIR where
  name : String
  source : String
  expression : Pgx.Constraint.TruthExpr
  validated : Bool := true
  deriving Repr, BEq, Inhabited

structure DomainIR where
  key : TypeKey
  base : TypeRef
  notNull : Bool
  defaultExpr : Option String := none
  /-- Legacy/raw normalized definitions retained for snapshot compatibility
  and diagnostics while the typed local constraints are populated by the
  Milestone-2 probe. -/
  constraints : Array String := #[]
  localConstraints : Array DomainConstraintIR := #[]
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

inductive ViewCheckOption where
  | none
  | local
  | cascaded
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ViewCheckOption

def tag : ViewCheckOption → String
  | .none => "none"
  | .local => "local"
  | .cascaded => "cascaded"

end ViewCheckOption

/-- Semantic metadata beyond the relation-shaped columns of a view.  Mutable
materialized-view population state is intentionally absent. -/
structure ViewIR where
  relation : RelationKey
  definition : String
  checkOption : ViewCheckOption := .none
  securityBarrier : Bool := false
  securityInvoker : Bool := false
  deriving Repr, BEq, Inhabited

inductive RoutineKind where
  | function
  | procedure
  | aggregate
  | window
  deriving Repr, BEq, DecidableEq, Inhabited

namespace RoutineKind

def tag : RoutineKind → String
  | .function => "function"
  | .procedure => "procedure"
  | .aggregate => "aggregate"
  | .window => "window"

end RoutineKind

inductive RoutineArgMode where
  | input
  | output
  | inputOutput
  | variadic
  | table
  deriving Repr, BEq, DecidableEq, Inhabited

namespace RoutineArgMode

def tag : RoutineArgMode → String
  | .input => "in"
  | .output => "out"
  | .inputOutput => "inout"
  | .variadic => "variadic"
  | .table => "table"

def isInput : RoutineArgMode → Bool
  | .input | .inputOutput | .variadic => true
  | .output | .table => false

end RoutineArgMode

structure RoutineArgIR where
  name : Option String := none
  mode : RoutineArgMode
  ty : TypeRef
  hasDefault : Bool := false
  deriving Repr, BEq, Inhabited

structure RoutineResultColumnIR where
  name : String
  ordinal : Nat
  ty : TypeRef
  /-- OUT/TABLE declarations carry no NOT NULL contract. -/
  nullable : Bool := true
  deriving Repr, BEq, Inhabited

/-- Catalog metadata for callable schema routines.  Literal SQL remains the
authority for an invocation; this metadata exposes stable overload and
table-valued result shapes without inventing cardinality or nullability. -/
structure RoutineIR where
  key : RoutineKey
  kind : RoutineKind
  args : Array RoutineArgIR
  returnsSet : Bool
  returnType : Option TypeRef := none
  resultColumns : Array RoutineResultColumnIR := #[]
  dynamicRecord : Bool := false
  strict : Bool := false
  volatility : String
  parallel : String
  securityDefiner : Bool := false
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

/-- Whether nulls compare as distinct values for a unique index/constraint. -/
inductive UniqueNullPolicy where
  | distinct
  | notDistinct
  deriving Repr, BEq, DecidableEq, Inhabited

namespace UniqueNullPolicy

def tag : UniqueNullPolicy → String
  | .distinct => "distinct"
  | .notDistinct => "not-distinct"

end UniqueNullPolicy

inductive ForeignKeyMatch where
  | simple
  | full
  | partialMatch
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ForeignKeyMatch

def tag : ForeignKeyMatch → String
  | .simple => "simple"
  | .full => "full"
  | .partialMatch => "partial"

end ForeignKeyMatch

inductive ForeignKeyAction where
  | noAction
  | restrict
  | cascade
  | setNull
  | setDefault
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ForeignKeyAction

def tag : ForeignKeyAction → String
  | .noAction => "no-action"
  | .restrict => "restrict"
  | .cascade => "cascade"
  | .setNull => "set-null"
  | .setDefault => "set-default"

end ForeignKeyAction

inductive IndexOrder where
  | ascending
  | descending
  deriving Repr, BEq, DecidableEq, Inhabited

namespace IndexOrder

def tag : IndexOrder → String
  | .ascending => "ascending"
  | .descending => "descending"

end IndexOrder

inductive IndexNullsOrder where
  | first
  | last
  deriving Repr, BEq, DecidableEq, Inhabited

namespace IndexNullsOrder

def tag : IndexNullsOrder → String
  | .first => "first"
  | .last => "last"

end IndexNullsOrder

/-- One key (not INCLUDE) element of a normalized index definition.  A key
is either a named column or an expression.  The resolved equality operator is
retained explicitly: relational uniqueness must not be inferred from Lean's
equality for the decoded column type. -/
structure IndexKeyElementIR where
  ordinal : Nat
  column : Option String := none
  expression : Option String := none
  collation : Option CollationKey := none
  opclass : Option QualifiedName := none
  equalityOperator : Option OperatorKey := none
  order : IndexOrder := .ascending
  nullsOrder : IndexNullsOrder := .last
  deriving Repr, BEq, Inhabited

/-- One aligned element of an exclusion constraint. -/
structure ExclusionElementIR where
  key : IndexKeyElementIR
  operator : OperatorKey
  deriving Repr, BEq, Inhabited

structure ConstraintIR where
  relation : RelationKey
  name : String
  kind : ConstraintKind
  columns : Array String := #[]
  referencedRelation : Option RelationKey := none
  referencedColumns : Array String := #[]
  expression : Option String := none
  /-- Typed local expression for `.check`; cross-row and non-check kinds keep
  this field empty and are never misrepresented as row predicates. -/
  localExpression : Option Pgx.Constraint.TruthExpr := none
  enforced : Bool := true
  validated : Bool := true
  deferrable : Bool := false
  initiallyDeferred : Bool := false
  /-- Parent constraint for a partition or inheritance child. -/
  parent : Option ConstraintKey := none
  isLocal : Bool := true
  inheritanceCount : Nat := 0
  noInherit : Bool := false
  period : Bool := false
  /-- Index implementing a primary, unique, foreign-key, or exclusion
  constraint when PostgreSQL records one. -/
  supportingIndex : Option IndexKey := none
  uniqueNullPolicy : UniqueNullPolicy := .distinct
  foreignKeyMatch : ForeignKeyMatch := .simple
  foreignKeyOnUpdate : ForeignKeyAction := .noAction
  foreignKeyOnDelete : ForeignKeyAction := .noAction
  /-- Referencing columns affected by a `DELETE ... SET NULL/DEFAULT` action.
  This collection is set-like, unlike the aligned key/operator vectors. -/
  foreignKeyDeleteSetColumns : Array String := #[]
  /-- Equality operators aligned with the key columns (`conpfeqop`). -/
  referencedToReferencingOperators : Array OperatorKey := #[]
  /-- Referenced-key equality operators (`conppeqop`). -/
  referencedEqualityOperators : Array OperatorKey := #[]
  /-- Referencing-key equality operators (`conffeqop`). -/
  referencingEqualityOperators : Array OperatorKey := #[]
  exclusionElements : Array ExclusionElementIR := #[]
  deriving Repr, BEq, Inhabited

namespace ConstraintIR

def key (constraint : ConstraintIR) : ConstraintKey := {
  relation := constraint.relation
  name := constraint.name
}

end ConstraintIR

structure IndexIR where
  relation : RelationKey
  name : String
  unique : Bool
  primary : Bool
  exclusion : Bool := false
  valid : Bool
  immediate : Bool := true
  ready : Bool := true
  live : Bool := true
  uniqueNullPolicy : UniqueNullPolicy := .distinct
  accessMethod : Option String := none
  columns : Array String := #[]
  keyElements : Array IndexKeyElementIR := #[]
  /-- Non-key INCLUDE columns, separated using `indnkeyatts`.  They do not
  participate in uniqueness or exclusion semantics. -/
  includedColumns : Array String := #[]
  predicate : Option String := none
  expression : Option String := none
  deriving Repr, BEq, Inhabited

namespace IndexIR

def key (index : IndexIR) : IndexKey := {
  schema := index.relation.schema
  name := index.name
}

end IndexIR

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
  /-- PostgreSQL wire type returned by Parse/Describe and checked before
  decoding. -/
  ty : TypeRef
  /-- Logical type recovered from a verified direct projection.  `none`
  means the logical type is exactly `ty`; `some` is decoded from the wire
  value and then locally validated/refined. -/
  logicalType : Option TypeRef := none
  nullable : Bool
  /-- The result was conservatively made nullable because plan inspection
  found an outer join or could not rule one out.  Such a cell does not prove
  that any source row exists, even when its catalog column was nullable. -/
  nullWidened : Bool := false
  origin : Option ColumnKey := none
  collation : Option CollationKey := none
  deriving Repr, BEq, Inhabited

structure QueryConstraintIR where
  relation : RelationKey
  name : String
  source : String
  expression : Pgx.Constraint.TruthExpr
  validated : Bool := true
  deriving Repr, BEq, Inhabited

structure QueryIR where
  name : String
  sql : String
  sqlHash : String
  params : Array ParamIR
  columns : Array QueryColumnIR
  /-- Relations for which plan inspection proved exactly one non-outer scan
  occurrence.  Only these relations can contribute same-row table checks;
  base relation/column OIDs alone cannot distinguish self-join aliases. -/
  rowPreservedRelations : Array RelationKey := #[]
  /-- Value-local source-row constraints whose complete identity projections
  are present in this result contract. -/
  localConstraints : Array QueryConstraintIR := #[]
  cardinality : Cardinality
  deriving Repr, BEq, Inhabited

structure SessionContract where
  searchPath : Array String
  timezone : String := "UTC"
  encoding : String := "UTF8"
  standardConformingStrings : Bool := true
  deriving Repr, BEq, Inhabited

/-- Escape hatch for an extension/user type.  `codec` names a Lean declaration
of type `Pgx.Typed.ResolvedCodec leanType`.  When that declaration is not
already exported by the runtime, `importModule` names the Lean module that
makes both declarations visible to generated code. -/
structure TypeOverrideIR where
  key : TypeKey
  leanType : String
  codec : String
  importModule : Option String := none
  deriving Repr, BEq, Inhabited

/-- Provenance for a reusable extension codec package.  Concrete Lean types
and codec declarations remain in `typeOverrides`; this record binds that set
to a required installed extension version and one import module. -/
structure ExtensionCodecPackageIR where
  extension : String
  version : String
  importModule : String
  types : Array TypeKey
  deriving Repr, BEq, Inhabited

structure DatabaseIR where
  /-- Version 4 adds normalized symbolic relational-constraint and supporting
  index semantics. -/
  formatVersion : Nat := 4
  serverMajor : Nat
  /-- Server majors which passed the generated contract's compatibility
  checks.  Empty is retained only for snapshots written before this field was
  introduced. -/
  supportedServerMajors : Array Nat := #[]
  serverFeatures : Array String := #[]
  session : SessionContract
  schemas : Array SchemaIR
  enums : Array EnumIR
  arrays : Array ArrayIR := #[]
  domains : Array DomainIR
  composites : Array CompositeIR := #[]
  ranges : Array RangeIR := #[]
  multiranges : Array MultirangeIR := #[]
  relations : Array RelationIR
  views : Array ViewIR := #[]
  routines : Array RoutineIR := #[]
  constraints : Array ConstraintIR
  indexes : Array IndexIR
  queries : Array QueryIR
  requiredExtensions : Array (String × String) := #[]
  typeOverrides : Array TypeOverrideIR := #[]
  extensionCodecPackages : Array ExtensionCodecPackageIR := #[]
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

private def collationKeyAtom (key : CollationKey) : String :=
  atom key.schema ++ atom key.name

private def routineKeyAtom (key : RoutineKey) : String :=
  atom key.schema ++ atom key.name ++ arrayAtom typeRefAtom key.inputTypes

private def qualifiedNameAtom (key : QualifiedName) : String :=
  atom key.schema ++ atom key.name

private def operatorKeyAtom (key : OperatorKey) : String :=
  atom key.schema ++ atom key.name ++ typeKeyAtom key.leftType ++
    typeKeyAtom key.rightType

private def constraintKeyAtom (key : ConstraintKey) : String :=
  relationKeyAtom key.relation ++ atom key.name

private def indexKeyAtom (key : IndexKey) : String :=
  atom key.schema ++ atom key.name

private def schemaAtom (schema : SchemaIR) : String :=
  atom schema.name

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

private def pgArrayAtom (value : ArrayIR) : String :=
  typeKeyAtom value.key ++ typeRefAtom value.element ++ atom value.delimiter

private def compositeFieldAtom (value : CompositeFieldIR) : String :=
  atom value.name ++ atom (toString value.ordinal) ++ typeRefAtom value.ty ++
    optionAtom collationKeyAtom value.collation

private def compositeAtom (value : CompositeIR) : String :=
  typeKeyAtom value.key ++ arrayAtom compositeFieldAtom value.fields

private def rangeAtom (value : RangeIR) : String :=
  typeKeyAtom value.key ++ typeRefAtom value.subtype ++
    typeKeyAtom value.multirange ++ optionAtom collationKeyAtom value.collation ++
    qualifiedNameAtom value.subtypeOpclass ++ optionAtom routineKeyAtom value.canonical ++
    optionAtom routineKeyAtom value.subtypeDiff

private def multirangeAtom (value : MultirangeIR) : String :=
  typeKeyAtom value.key ++ typeKeyAtom value.range

private def scalarKindAtom : Pgx.Constraint.ScalarKind → String
  | .boolean => "boolean"
  | .int16 => "int16"
  | .int32 => "int32"
  | .int64 => "int64"
  | .numeric => "numeric"
  | .text => "text"
  | .enumeration key => "enumeration" ++ typeKeyAtom key

private def scalarTypeAtom (value : Pgx.Constraint.ScalarType) : String :=
  typeRefAtom value.declared ++ atom (scalarKindAtom value.base) ++
    arrayAtom typeKeyAtom value.domains

private def literalAtom : Pgx.Constraint.Literal → String
  | .null => "null"
  | .boolean value => "boolean" ++ boolAtom value
  | .integer value => "integer" ++ atom (toString value)
  | .numeric value => "numeric" ++ atom value
  | .text value => "text" ++ atom value
  | .enumeration key label => "enumeration" ++ typeKeyAtom key ++ atom label

private def castPreservationAtom : Pgx.Constraint.CastPreservation → String
  | .identity => "identity"
  | .domain => "domain"
  | .integerWiden => "integer-widen"
  | .exactNumeric => "exact-numeric"
  | .textRepresentation => "text-representation"
  | .enumLiteral => "enum-literal"

private partial def valueExprAtom : Pgx.Constraint.ValueExpr → String
  | .column name ty nullable =>
      "column" ++ atom name ++ scalarTypeAtom ty ++ boolAtom nullable
  | .domainValue ty nullable =>
      "domain-value" ++ scalarTypeAtom ty ++ boolAtom nullable
  | .literal value ty => "literal" ++ literalAtom value ++ scalarTypeAtom ty
  | .cast preservation value target =>
      "cast" ++ atom (castPreservationAtom preservation) ++
        atom (valueExprAtom value) ++ scalarTypeAtom target
  | .neg value result =>
      "neg" ++ atom (valueExprAtom value) ++ scalarTypeAtom result
  | .add left right result =>
      "add" ++ atom (valueExprAtom left) ++ atom (valueExprAtom right) ++
        scalarTypeAtom result
  | .sub left right result =>
      "sub" ++ atom (valueExprAtom left) ++ atom (valueExprAtom right) ++
        scalarTypeAtom result
  | .charLength value result =>
      "char-length" ++ atom (valueExprAtom value) ++ scalarTypeAtom result
  | .btrim value result =>
      "btrim" ++ atom (valueExprAtom value) ++ scalarTypeAtom result
  | .position substring string result =>
      "position" ++ atom (valueExprAtom substring) ++ atom (valueExprAtom string) ++
        scalarTypeAtom result

private def comparisonAtom : Pgx.Constraint.Comparison → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt => "lt"
  | .le => "le"
  | .gt => "gt"
  | .ge => "ge"

private partial def truthExprAtom : Pgx.Constraint.TruthExpr → String
  | .constant value =>
      "constant" ++ optionAtom boolAtom value
  | .fromBoolean value => "from-boolean" ++ atom (valueExprAtom value)
  | .compare op left right =>
      "compare" ++ atom (comparisonAtom op) ++ atom (valueExprAtom left) ++
        atom (valueExprAtom right)
  | .isNull value => "is-null" ++ atom (valueExprAtom value)
  | .isNotNull value => "is-not-null" ++ atom (valueExprAtom value)
  | .and left right =>
      "and" ++ atom (truthExprAtom left) ++ atom (truthExprAtom right)
  | .or left right =>
      "or" ++ atom (truthExprAtom left) ++ atom (truthExprAtom right)
  | .not value => "not" ++ atom (truthExprAtom value)

private def domainConstraintAtom (value : DomainConstraintIR) : String :=
  atom value.name ++ atom value.source ++ atom (truthExprAtom value.expression) ++
    boolAtom value.validated

private def domainAtom (value : DomainIR) : String :=
  typeKeyAtom value.key ++ typeRefAtom value.base ++ boolAtom value.notNull ++
    optionAtom atom value.defaultExpr ++ arrayAtom id value.constraints ++
    arrayAtom domainConstraintAtom value.localConstraints

private def viewAtom (value : ViewIR) : String :=
  relationKeyAtom value.relation ++ atom value.definition ++
    atom value.checkOption.tag ++ boolAtom value.securityBarrier ++
    boolAtom value.securityInvoker

private def routineArgAtom (value : RoutineArgIR) : String :=
  optionAtom atom value.name ++ atom value.mode.tag ++ typeRefAtom value.ty ++
    boolAtom value.hasDefault

private def routineResultColumnAtom (value : RoutineResultColumnIR) : String :=
  atom value.name ++ atom (toString value.ordinal) ++ typeRefAtom value.ty ++
    boolAtom value.nullable

private def routineAtom (value : RoutineIR) : String :=
  routineKeyAtom value.key ++ atom value.kind.tag ++
    arrayAtom routineArgAtom value.args ++ boolAtom value.returnsSet ++
    optionAtom typeRefAtom value.returnType ++
    arrayAtom routineResultColumnAtom value.resultColumns ++
    boolAtom value.dynamicRecord ++ boolAtom value.strict ++
    atom value.volatility ++ atom value.parallel ++ boolAtom value.securityDefiner

private def indexKeyElementAtom (value : IndexKeyElementIR) : String :=
  atom (toString value.ordinal) ++ optionAtom atom value.column ++
    optionAtom atom value.expression ++ optionAtom collationKeyAtom value.collation ++
    optionAtom qualifiedNameAtom value.opclass ++
    optionAtom operatorKeyAtom value.equalityOperator ++ atom value.order.tag ++
    atom value.nullsOrder.tag

private def exclusionElementAtom (value : ExclusionElementIR) : String :=
  indexKeyElementAtom value.key ++ operatorKeyAtom value.operator

private def constraintAtom (value : ConstraintIR) : String :=
  relationKeyAtom value.relation ++ atom value.name ++ atom value.kind.tag ++
    arrayAtom id value.columns ++ optionAtom relationKeyAtom value.referencedRelation ++
    arrayAtom id value.referencedColumns ++ optionAtom atom value.expression ++
    optionAtom truthExprAtom value.localExpression ++
    boolAtom value.enforced ++ boolAtom value.validated ++
    boolAtom value.deferrable ++ boolAtom value.initiallyDeferred ++
    optionAtom constraintKeyAtom value.parent ++ boolAtom value.isLocal ++
    atom (toString value.inheritanceCount) ++ boolAtom value.noInherit ++
    boolAtom value.period ++ optionAtom indexKeyAtom value.supportingIndex ++
    atom value.uniqueNullPolicy.tag ++ atom value.foreignKeyMatch.tag ++
    atom value.foreignKeyOnUpdate.tag ++ atom value.foreignKeyOnDelete.tag ++
    arrayAtom id value.foreignKeyDeleteSetColumns ++
    arrayAtom operatorKeyAtom value.referencedToReferencingOperators ++
    arrayAtom operatorKeyAtom value.referencedEqualityOperators ++
    arrayAtom operatorKeyAtom value.referencingEqualityOperators ++
    arrayAtom exclusionElementAtom value.exclusionElements

private def indexAtom (value : IndexIR) : String :=
  relationKeyAtom value.relation ++ atom value.name ++ boolAtom value.unique ++
    boolAtom value.primary ++ boolAtom value.exclusion ++ boolAtom value.valid ++
    boolAtom value.immediate ++ boolAtom value.ready ++ boolAtom value.live ++
    atom value.uniqueNullPolicy.tag ++ optionAtom atom value.accessMethod ++
    arrayAtom id value.columns ++ arrayAtom indexKeyElementAtom value.keyElements ++
    arrayAtom id value.includedColumns ++ optionAtom atom value.predicate ++
    optionAtom atom value.expression

private def overrideAtom (value : TypeOverrideIR) : String :=
  typeKeyAtom value.key ++ atom value.leanType ++ atom value.codec ++
    optionAtom atom value.importModule

private def extensionCodecPackageAtom (value : ExtensionCodecPackageIR) : String :=
  atom value.extension ++ atom value.version ++ atom value.importModule ++
    arrayAtom typeKeyAtom value.types

private def queryColumnAtom (column : QueryColumnIR) : String :=
  atom column.name ++ typeRefAtom column.ty ++
    optionAtom typeRefAtom column.logicalType ++ boolAtom column.nullable ++
    boolAtom column.nullWidened ++
    optionAtom (fun origin => relationKeyAtom origin.relation ++ atom origin.name) column.origin

private def queryConstraintAtom (constraint : QueryConstraintIR) : String :=
  relationKeyAtom constraint.relation ++ atom constraint.name ++ atom constraint.source ++
    atom (truthExprAtom constraint.expression) ++ boolAtom constraint.validated

private def paramAtom (param : ParamIR) : String :=
  atom (toString param.position) ++ atom param.name ++ typeRefAtom param.ty ++
    boolAtom param.nullable

private def queryAtom (query : QueryIR) : String :=
  atom query.name ++ atom query.sqlHash ++ arrayAtom paramAtom query.params ++
    arrayAtom queryColumnAtom query.columns ++
    arrayAtom relationKeyAtom query.rowPreservedRelations ++
    arrayAtom queryConstraintAtom query.localConstraints ++ atom query.cardinality.tag

private def sortByAtom (f : α → String) (values : Array α) : Array α :=
  (values.toList.mergeSort fun left right =>
    compare (f left) (f right) == Ordering.lt).toArray

private def sortNats (values : Array Nat) : Array Nat :=
  values.toList.mergeSort (· < ·) |>.toArray

private def relationColumnLess
    (left right : RelationColumnIR) : Bool :=
  match compare left.ordinal right.ordinal with
  | .lt => true
  | .gt => false
  | .eq =>
      match compare left.name right.name with
      | .lt => true
      | .gt => false
      | .eq => compare (relationColumnAtom left) (relationColumnAtom right) == Ordering.lt

private def paramLess (left right : ParamIR) : Bool :=
  match compare left.position right.position with
  | .lt => true
  | .gt => false
  | .eq =>
      match compare left.name right.name with
      | .lt => true
      | .gt => false
      | .eq => compare (paramAtom left) (paramAtom right) == Ordering.lt

private def indexKeyElementLess
    (left right : IndexKeyElementIR) : Bool :=
  match compare left.ordinal right.ordinal with
  | .lt => true
  | .gt => false
  | .eq => compare (indexKeyElementAtom left) (indexKeyElementAtom right) == Ordering.lt

private def exclusionElementLess
    (left right : ExclusionElementIR) : Bool :=
  match compare left.key.ordinal right.key.ordinal with
  | .lt => true
  | .gt => false
  | .eq => compare (exclusionElementAtom left) (exclusionElementAtom right) == Ordering.lt

private def normalizeDomain (domain : DomainIR) : DomainIR :=
  { domain with
    constraints := sortByAtom id domain.constraints
    localConstraints := sortByAtom domainConstraintAtom domain.localConstraints }

private def normalizeRelation (relation : RelationIR) : RelationIR :=
  { relation with columns := relation.columns.toList.mergeSort relationColumnLess |>.toArray }

private def normalizeQuery (query : QueryIR) : QueryIR :=
  { query with
    params := query.params.toList.mergeSort paramLess |>.toArray
    rowPreservedRelations := sortByAtom relationKeyAtom query.rowPreservedRelations
    localConstraints := sortByAtom queryConstraintAtom query.localConstraints }

private def normalizeComposite (value : CompositeIR) : CompositeIR :=
  { value with fields := value.fields.toList.mergeSort (fun left right =>
      if left.ordinal == right.ordinal then
        compare (compositeFieldAtom left) (compositeFieldAtom right) == Ordering.lt
      else left.ordinal < right.ordinal) |>.toArray }

private def normalizePackage (value : ExtensionCodecPackageIR) : ExtensionCodecPackageIR :=
  { value with types := sortByAtom typeKeyAtom value.types }

private def normalizeConstraint (value : ConstraintIR) : ConstraintIR :=
  { value with
    foreignKeyDeleteSetColumns :=
      sortByAtom id value.foreignKeyDeleteSetColumns
    exclusionElements :=
      value.exclusionElements.toList.mergeSort exclusionElementLess |>.toArray }

private def normalizeIndex (value : IndexIR) : IndexIR :=
  { value with
    keyElements := value.keyElements.toList.mergeSort indexKeyElementLess |>.toArray
    includedColumns := sortByAtom id value.includedColumns }

/-- Put every unordered IR collection in a stable order before serialization.
Arrays whose order is part of PostgreSQL semantics (including enum labels,
query result columns, constraint/index columns, aligned operator vectors, and
`search_path`) are deliberately preserved. -/
def DatabaseIR.normalize (db : DatabaseIR) : DatabaseIR :=
  let domains := db.domains.map normalizeDomain
  let composites := db.composites.map normalizeComposite
  let relations := db.relations.map normalizeRelation
  let queries := db.queries.map normalizeQuery
  let packages := db.extensionCodecPackages.map normalizePackage
  let constraints := db.constraints.map normalizeConstraint
  let indexes := db.indexes.map normalizeIndex
  { db with
    supportedServerMajors := sortNats db.supportedServerMajors
    serverFeatures := sortByAtom id db.serverFeatures
    schemas := sortByAtom schemaAtom db.schemas
    enums := sortByAtom enumAtom db.enums
    arrays := sortByAtom pgArrayAtom db.arrays
    domains := sortByAtom domainAtom domains
    composites := sortByAtom compositeAtom composites
    ranges := sortByAtom rangeAtom db.ranges
    multiranges := sortByAtom multirangeAtom db.multiranges
    relations := sortByAtom relationAtom relations
    views := sortByAtom viewAtom db.views
    routines := sortByAtom routineAtom db.routines
    constraints := sortByAtom constraintAtom constraints
    indexes := sortByAtom indexAtom indexes
    queries := sortByAtom queryAtom queries
    requiredExtensions := sortByAtom (fun value => atom value.1 ++ atom value.2)
      db.requiredExtensions
    typeOverrides := sortByAtom overrideAtom db.typeOverrides
    extensionCodecPackages := sortByAtom extensionCodecPackageAtom packages }

private def databaseMaterial (includeServerMajor : Bool) (db : DatabaseIR) : String :=
  atom (toString db.formatVersion) ++
    (if includeServerMajor then atom (toString db.serverMajor) else "") ++
    arrayAtom (fun value => toString value) db.supportedServerMajors ++
    arrayAtom id db.serverFeatures ++ arrayAtom id db.session.searchPath ++ atom db.session.timezone ++
    atom db.session.encoding ++ boolAtom db.session.standardConformingStrings ++
    arrayAtom schemaAtom db.schemas ++ arrayAtom enumAtom db.enums ++
    arrayAtom pgArrayAtom db.arrays ++ arrayAtom domainAtom db.domains ++
    arrayAtom compositeAtom db.composites ++ arrayAtom rangeAtom db.ranges ++
    arrayAtom multirangeAtom db.multiranges ++
    arrayAtom relationAtom db.relations ++ arrayAtom viewAtom db.views ++
    arrayAtom routineAtom db.routines ++
    arrayAtom constraintAtom db.constraints ++
    arrayAtom indexAtom (db.indexes.filter fun value =>
      value.unique || value.primary || value.exclusion) ++
    arrayAtom queryAtom db.queries ++ arrayAtom (fun value =>
      atom value.1 ++ atom value.2) db.requiredExtensions ++
    arrayAtom overrideAtom db.typeOverrides ++
    arrayAtom extensionCodecPackageAtom db.extensionCodecPackages

/-- Canonical material for the type-relevant contract.  Physical OIDs, ACLs,
owners, and performance-only index details cannot influence it. -/
def DatabaseIR.contractMaterial (db : DatabaseIR) : String :=
  databaseMaterial true db.normalize

/-- Canonical material used to compare contracts produced by different
PostgreSQL majors.  It differs from `contractMaterial` only by omitting the
server major itself. -/
def DatabaseIR.compatibilityMaterial (db : DatabaseIR) : String :=
  databaseMaterial false db.normalize

def DatabaseIR.contractHashBytes (db : DatabaseIR) : ByteArray :=
  Pg.Crypto.sha256 db.contractMaterial.toUTF8

def DatabaseIR.contractHash (db : DatabaseIR) : String :=
  Pg.Crypto.toHexLower db.contractHashBytes

def DatabaseIR.compatibilityHashBytes (db : DatabaseIR) : ByteArray :=
  Pg.Crypto.sha256 db.compatibilityMaterial.toUTF8

def DatabaseIR.compatibilityHash (db : DatabaseIR) : String :=
  Pg.Crypto.toHexLower db.compatibilityHashBytes

end Pgx
