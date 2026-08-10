module

public import Pgx.IR.Core

public section

/-!
# Typed local PostgreSQL constraint expressions

This module contains the normalized, executable subset of PostgreSQL check
expressions.  It deliberately distinguishes scalar values from SQL truth
values: a nullable comparison produces `unknown`, and PostgreSQL accepts a
check whenever its result is either `true` or `unknown`.

The parser is responsible for constructing well-typed terms.  Constructors
remain data-only so the IR can be fingerprinted and serialized without
depending on PostgreSQL's private expression tree representation.
-/

namespace Pgx.Constraint

/-- Scalar semantics modeled by the local-refinement layer. -/
inductive ScalarKind where
  | boolean
  | int16
  | int32
  | int64
  | numeric
  | text
  | enumeration (key : Pgx.TypeKey)
  deriving Repr, BEq, Inhabited

/-- A scalar's declared PostgreSQL type and its fully unwrapped semantics.
`domains` is ordered outermost first, making nested domain identity explicit. -/
structure ScalarType where
  declared : Pgx.TypeRef
  base : ScalarKind
  domains : Array Pgx.TypeKey := #[]
  deriving Repr, BEq, Inhabited

namespace ScalarType

def isBoolean (ty : ScalarType) : Bool := ty.base matches .boolean

def isInteger (ty : ScalarType) : Bool :=
  match ty.base with
  | .int16 | .int32 | .int64 => true
  | _ => false

def isExactNumeric (ty : ScalarType) : Bool :=
  ty.isInteger || ty.base matches .numeric

def isText (ty : ScalarType) : Bool := ty.base matches .text

def display (ty : ScalarType) : String := ty.declared.key.display

end ScalarType

/-- Exact literal payloads.  `numeric` retains canonical decimal text rather
than rounding through a floating-point representation. -/
inductive Literal where
  | null
  | boolean (value : Bool)
  | integer (value : Int)
  | numeric (canonical : String)
  | text (value : String)
  | enumeration (key : Pgx.TypeKey) (label : String)
  deriving Repr, BEq, Inhabited

/-- Why a cast is known not to change the modeled value. -/
inductive CastPreservation where
  | identity
  | domain
  | integerWiden
  | exactNumeric
  | textRepresentation
  | enumLiteral
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed scalar expression.  The result type is recorded on every operation
whose PostgreSQL overload resolution affects it. -/
inductive ValueExpr where
  | column (name : String) (ty : ScalarType) (nullable : Bool)
  | domainValue (ty : ScalarType) (nullable : Bool)
  | literal (value : Literal) (ty : ScalarType)
  | cast (preservation : CastPreservation) (value : ValueExpr) (target : ScalarType)
  | neg (value : ValueExpr) (result : ScalarType)
  | add (left right : ValueExpr) (result : ScalarType)
  | sub (left right : ValueExpr) (result : ScalarType)
  | charLength (value : ValueExpr) (result : ScalarType)
  | btrim (value : ValueExpr) (result : ScalarType)
  | position (substring string : ValueExpr) (result : ScalarType)
  deriving Repr, BEq, Inhabited

namespace ValueExpr

def type : ValueExpr → ScalarType
  | .column _ ty _ | .domainValue ty _ | .literal _ ty
  | .cast _ _ ty | .neg _ ty | .add _ _ ty | .sub _ _ ty
  | .charLength _ ty | .btrim _ ty | .position _ _ ty => ty

/-- Conservative SQL-nullability.  This is exact for the supported primitive
operations except that it intentionally does not simplify expressions. -/
def nullable : ValueExpr → Bool
  | .column _ _ nullable | .domainValue _ nullable => nullable
  | .literal .null _ => true
  | .literal _ _ => false
  | .cast _ value _ | .neg value _ | .charLength value _ | .btrim value _ => value.nullable
  | .add left right _ | .sub left right _ => left.nullable || right.nullable
  | .position substring string _ => substring.nullable || string.nullable

def referencedColumns : ValueExpr → Array String
  | .column name _ _ => #[name]
  | .domainValue .. | .literal .. => #[]
  | .cast _ value _ | .neg value _ | .charLength value _ | .btrim value _ =>
      value.referencedColumns
  | .add left right _ | .sub left right _ =>
      left.referencedColumns ++ right.referencedColumns
  | .position substring string _ =>
      substring.referencedColumns ++ string.referencedColumns

end ValueExpr

inductive Comparison where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A typed expression with PostgreSQL three-valued Boolean semantics. -/
inductive TruthExpr where
  /-- `none` denotes SQL `unknown`. -/
  | constant (value : Option Bool)
  | fromBoolean (value : ValueExpr)
  | compare (op : Comparison) (left right : ValueExpr)
  | isNull (value : ValueExpr)
  | isNotNull (value : ValueExpr)
  | and (left right : TruthExpr)
  | or (left right : TruthExpr)
  | not (value : TruthExpr)
  deriving Repr, BEq, Inhabited

namespace TruthExpr

/-- Whether evaluation can produce SQL `unknown`. -/
def nullable : TruthExpr → Bool
  | .constant value => value.isNone
  | .fromBoolean value => value.nullable
  | .compare _ left right => left.nullable || right.nullable
  | .isNull _ | .isNotNull _ => false
  | .and left right | .or left right => left.nullable || right.nullable
  | .not value => value.nullable

def referencedColumns : TruthExpr → Array String
  | .constant _ => #[]
  | .fromBoolean value | .isNull value | .isNotNull value => value.referencedColumns
  | .compare _ left right => left.referencedColumns ++ right.referencedColumns
  | .and left right | .or left right =>
      left.referencedColumns ++ right.referencedColumns
  | .not value => value.referencedColumns

end TruthExpr

/-- PostgreSQL's three truth values. -/
inductive SqlTruth where
  | true
  | false
  | unknown
  deriving Repr, BEq, DecidableEq, Inhabited

namespace SqlTruth

/-- A PostgreSQL `CHECK` rejects only false; null/unknown passes. -/
@[expose] def checkPasses : SqlTruth → Prop
  | .false => False
  | .true | .unknown => True

instance (value : SqlTruth) : Decidable value.checkPasses :=
  match value with
  | .false => isFalse id
  | .true | .unknown => isTrue trivial

end SqlTruth

/-- Stable classes used by generator diagnostics and acceptance tests. -/
inductive DiagnosticCategory where
  | syntax
  | unsupportedFunction
  | unsupportedOperator
  | unsupportedType
  | unknownIdentifier
  | ambiguousIdentifier
  | unsafeCast
  | typeMismatch
  | invalidLiteral
  | nonBooleanCheck
  | trailingInput
  deriving Repr, BEq, DecidableEq, Inhabited

namespace DiagnosticCategory

def tag : DiagnosticCategory → String
  | .syntax => "syntax"
  | .unsupportedFunction => "unsupported-function"
  | .unsupportedOperator => "unsupported-operator"
  | .unsupportedType => "unsupported-type"
  | .unknownIdentifier => "unknown-identifier"
  | .ambiguousIdentifier => "ambiguous-identifier"
  | .unsafeCast => "unsafe-cast"
  | .typeMismatch => "type-mismatch"
  | .invalidLiteral => "invalid-literal"
  | .nonBooleanCheck => "non-boolean-check"
  | .trailingInput => "trailing-input"

end DiagnosticCategory

structure Diagnostic where
  category : DiagnosticCategory
  /-- Zero-based Unicode scalar offset into `pg_get_constraintdef` output. -/
  offset : Nat
  message : String
  deriving Repr, BEq, Inhabited

namespace Diagnostic

def toMessage (diagnostic : Diagnostic) : String :=
  s!"constraint expression at offset {diagnostic.offset} \
    [{diagnostic.category.tag}]: {diagnostic.message}"

end Diagnostic

instance : ToString Diagnostic := ⟨Diagnostic.toMessage⟩

/-- Parsed and typechecked local check, retaining the normalized server text
for diagnostics while making the typed expression authoritative. -/
structure Parsed where
  source : String
  expression : TruthExpr
  /-- Whether the normalized definition omitted PostgreSQL's `NOT VALID`
  suffix.  Probes cross-check this deparsed property against `convalidated`. -/
  validated : Bool := true
  deriving Repr, BEq, Inhabited

end Pgx.Constraint
