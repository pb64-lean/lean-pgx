import Pgx.Codegen.ConstraintParser

namespace Pgx.Test.ConstraintParser

open Pgx.Constraint
open Pgx.Codegen.ConstraintParser

private def base (name : String) (typmod : Option Int32 := none) : Pgx.TypeRef := {
  key := { schema := "pg_catalog", name, kind := .base }
  typmod
}

private def statusKey : Pgx.TypeKey := {
  schema := "app"
  name := "user_status"
  kind := .enum
}

private def trimmedKey : Pgx.TypeKey := {
  schema := "app"
  name := "trimmed_text"
  kind := .domain
}

private def emailKey : Pgx.TypeKey := {
  schema := "app"
  name := "email_address"
  kind := .domain
}

private def status : Pgx.EnumIR := {
  key := statusKey
  labels := #["active", "disabled"]
}

private def trimmed : Pgx.DomainIR := {
  key := trimmedKey
  base := base "text"
  notNull := false
}

private def email : Pgx.DomainIR := {
  key := emailKey
  base := { key := trimmedKey }
  notNull := true
}

private def users : Pgx.RelationIR := {
  key := { schema := "app", name := "users" }
  kind := .table
  columns := #[
    { name := "age", ordinal := 1, ty := base "int4", nullable := true },
    { name := "status", ordinal := 2, ty := { key := statusKey }, nullable := false },
    { name := "display_name", ordinal := 3, ty := base "varchar" (some 68), nullable := false },
    { name := "amount", ordinal := 4, ty := base "numeric", nullable := false }
  ]
}

private def deterministic : Options := { deterministicTextEquality := true }

private def expectCategory {α : Type} (category : DiagnosticCategory)
    (result : Except Diagnostic α) : IO Unit :=
  match result with
  | .error error => do
      unless error.category == category do
        panic! s!"expected {category.tag}, received {error.category.tag}: {error}"
  | .ok _ => panic! s!"expected {category.tag} diagnostic"

private def expectDiagnostic {α : Type} (category : DiagnosticCategory)
    (offset : Nat) (message : String) (result : Except Diagnostic α) : IO Unit :=
  match result with
  | .ok _ => panic! s!"expected {category.tag} diagnostic"
  | .error error => do
      unless error.category == category do
        panic! s!"expected {category.tag}, received {error.category.tag}: {error}"
      unless error.offset > 0 do
        panic! s!"diagnostic offset must be nonzero: {error}"
      unless error.offset == offset do
        panic! s!"expected offset {offset}, received {error.offset}: {error}"
      unless error.message == message do
        panic! s!"expected message {repr message}, received {repr error.message}"

private partial def hasBtrimValue : ValueExpr → Bool
  | .btrim .. => true
  | .cast _ value _ | .neg value _ | .charLength value _ => hasBtrimValue value
  | .add left right _ | .sub left right _ | .position left right _ =>
      hasBtrimValue left || hasBtrimValue right
  | _ => false

private partial def hasPositionValue : ValueExpr → Bool
  | .position .. => true
  | .cast _ value _ | .neg value _ | .charLength value _ | .btrim value _ =>
      hasPositionValue value
  | .add left right _ | .sub left right _ =>
      hasPositionValue left || hasPositionValue right
  | _ => false

private partial def hasNestedDomain : ValueExpr → Bool
  | .domainValue ty _ => ty.domains == #[emailKey, trimmedKey]
  | .cast _ value _ | .neg value _ | .charLength value _ | .btrim value _ =>
      hasNestedDomain value
  | .add left right _ | .sub left right _ | .position left right _ =>
      hasNestedDomain left || hasNestedDomain right
  | _ => false

private partial def anyValue (predicate : ValueExpr → Bool) : TruthExpr → Bool
  | .constant _ => false
  | .fromBoolean value | .isNull value | .isNotNull value => predicate value
  | .compare _ left right => predicate left || predicate right
  | .and left right | .or left right => anyValue predicate left || anyValue predicate right
  | .not value => anyValue predicate value

def main : IO Unit := do
  let tableCheck ← match parseTableCheck users #[status] #[trimmed, email]
      "CHECK (((age IS NULL) OR ((age >= 0) AND (status = 'active'::app.user_status))))" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! tableCheck.expression.referencedColumns.contains "age"
  assert! tableCheck.expression.referencedColumns.contains "status"
  assert! tableCheck.expression.nullable

  let domainCheck ← match parseDomainCheck email #[status] #[trimmed, email]
      "CHECK (((btrim((VALUE)::text) <> ''::text) AND \
        (POSITION(('@'::text) IN ((VALUE)::text)) > 1)))" deterministic with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! anyValue hasBtrimValue domainCheck.expression
  assert! anyValue hasPositionValue domainCheck.expression
  assert! anyValue hasNestedDomain domainCheck.expression
  assert! domainCheck.expression.nullable

  let lengthCheck ← match parseTableCheck users #[status] #[trimmed, email]
      "CHECK ((pg_catalog.char_length((display_name)::text) <= 64))" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! lengthCheck.expression.referencedColumns == #["display_name"]

  expectDiagnostic .unsupportedFunction 7
    "function lower is not supported in local constraints" <|
    parseTableCheck users #[status] #[trimmed, email]
    "CHECK (lower(display_name) = 'someone'::text)" deterministic
  expectDiagnostic .unsupportedOperator 20
    "operator ~ is not supported in local constraints" <|
    parseTableCheck users #[status] #[trimmed, email]
    "CHECK (display_name ~ '^[a-z]+$'::text)" deterministic
  expectDiagnostic .unsupportedType 14
    "pg_catalog.numeric comparisons are unsupported because exact ordering is not modeled" <|
    parseTableCheck users #[status] #[trimmed, email]
    "CHECK (amount >= 1.25)"
  expectCategory .unsupportedOperator <| parseTableCheck users #[status] #[trimmed, email]
    "CHECK (display_name = 'someone'::text)"
  expectCategory .unsupportedOperator <| parseTableCheck users #[status] #[trimmed, email]
    "CHECK (display_name < 'someone'::text)" deterministic
  expectCategory .unsupportedOperator <| parseTableCheck users #[status] #[trimmed, email]
    "CHECK ((age + 1) > 0)"
  expectDiagnostic .unsafeCast 11
    "cast from pg_catalog.int4 (base) to pg_catalog.int2 (base) is not known to preserve modeled values" <|
    parseTableCheck users #[status] #[trimmed, email]
    "CHECK ((age::int2) >= 0)"
  expectDiagnostic .unknownIdentifier 7 "unknown constraint column missing" <|
    parseTableCheck users #[status] #[trimmed, email]
    "CHECK (missing >= 0)"
  expectCategory .invalidLiteral <| parseTableCheck users #[status] #[trimmed, email]
    "CHECK (status = 'pending'::app.user_status)"
  expectDiagnostic .typeMismatch 11
    "incompatible operand types pg_catalog.int4 (base) and app.user_status (enum)" <|
    parseTableCheck users #[status] #[trimmed, email]
    "CHECK (age = status)"
  expectDiagnostic .nonBooleanCheck 7
    "check expression has scalar type pg_catalog.int4 (base), not Boolean" <|
    parseTableCheck users #[status] #[trimmed, email]
    "CHECK (age)"
  expectCategory .typeMismatch <| parseTableCheck users #[status] #[trimmed, email]
    "CHECK (btrim(display_name, 'x'::text) = display_name)" deterministic

  IO.println "PASS typed PostgreSQL constraint parser"

end Pgx.Test.ConstraintParser

def main : IO Unit :=
  Pgx.Test.ConstraintParser.main
