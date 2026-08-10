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

private def checkedKey : Pgx.TypeKey := {
  schema := "app"
  name := "checked_text"
  kind := .domain
}

private def limitedKey : Pgx.TypeKey := {
  schema := "app"
  name := "limited_text"
  kind := .domain
}

private def wideIntKey : Pgx.TypeKey := {
  schema := "app"
  name := "wide_int"
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

private def checked : Pgx.DomainIR := {
  key := checkedKey
  base := base "text"
  notNull := false
  localConstraints := #[{
    name := "checked_text_check"
    source := "CHECK (false)"
    expression := .constant (some false)
  }]
}

private def limited : Pgx.DomainIR := {
  key := limitedKey
  base := base "varchar" (some 7)
  notNull := false
}

private def wideInt : Pgx.DomainIR := {
  key := wideIntKey
  base := base "int8"
  notNull := false
}

private def users : Pgx.RelationIR := {
  key := { schema := "app", name := "users" }
  kind := .table
  columns := #[
    { name := "age", ordinal := 1, ty := base "int4", nullable := true },
    { name := "status", ordinal := 2, ty := { key := statusKey }, nullable := false },
    { name := "display_name", ordinal := 3, ty := base "varchar" (some 68), nullable := false },
    { name := "amount", ordinal := 4, ty := base "numeric", nullable := false },
    { name := "code", ordinal := 5, ty := base "bpchar" (some 7), nullable := false },
    { name := "email", ordinal := 6, ty := { key := emailKey }, nullable := false },
    { name := "checked_value", ordinal := 7, ty := { key := checkedKey }, nullable := false },
    { name := "small_count", ordinal := 8, ty := base "int2", nullable := false },
    { name := "big_count", ordinal := 9, ty := base "int8", nullable := false }
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

private partial def hasDomainUnwrap : ValueExpr → Bool
  | .cast .domain value target =>
      (!value.type.domains.isEmpty && target.domains.isEmpty) || hasDomainUnwrap value
  | .cast _ value _ | .neg value _ | .charLength value _ | .btrim value _ =>
      hasDomainUnwrap value
  | .add left right _ | .sub left right _ | .position left right _ =>
      hasDomainUnwrap left || hasDomainUnwrap right
  | _ => false

private partial def anyValue (predicate : ValueExpr → Bool) : TruthExpr → Bool
  | .constant _ => false
  | .fromBoolean value | .isNull value | .isNotNull value => predicate value
  | .compare _ left right => predicate left || predicate right
  | .and left right | .or left right => anyValue predicate left || anyValue predicate right
  | .not value => anyValue predicate value

private partial def integerLiteral? : ValueExpr → Option (Int × ScalarType)
  | .literal (.integer value) ty => some (value, ty)
  | .cast .identity value _ => integerLiteral? value
  | _ => none

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

  -- PostgreSQL quotes integer constants that do not fit its initially chosen
  -- int4 literal type, then records the selected fixed-width type as a cast.
  -- These three forms must remain exact integer literals in the typed IR.
  for (source, expectedValue, expectedType) in #[
      ("CHECK (small_count <= '32767'::smallint)", (32767 : Int), base "int2"),
      ("CHECK (age <= '2147483647'::integer)", (2147483647 : Int), base "int4"),
      ("CHECK (big_count < '4294967296'::bigint)", (4294967296 : Int), base "int8")
    ] do
    let parsed ← match parseTableCheck users #[status] #[trimmed, email] source with
      | .ok parsed => pure parsed
      | .error error => panic! s!"deparsed integer cast {source}: {error}"
    match parsed.expression with
    | .compare _ _ right =>
        let some (value, ty) := integerLiteral? right
          | panic! s!"deparsed integer cast did not produce an integer literal: {source}"
        assert! value == expectedValue
        assert! ty.declared == expectedType
    | _ => panic! s!"deparsed integer cast did not produce a comparison: {source}"

  expectDiagnostic .invalidLiteral 19
    "\"not-an-int\" is not a valid PostgreSQL integer literal for pg_catalog.int8 (base)" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (big_count < 'not-an-int'::bigint)"
  expectDiagnostic .invalidLiteral 22
    "integer literal 32768 is outside pg_catalog.int2 (base)" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (small_count <= '32768'::smallint)"
  expectDiagnostic .invalidLiteral 19
    "integer literal 9223372036854775808 is outside pg_catalog.int8 (base)" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (big_count < '9223372036854775808'::bigint)"

  for (serverMajor, source) in #[(17, "CHECK (age >= 0) NOT VALID"),
      (18, "CHECK (age >= 0) NOT VALID")] do
    let parsed ← match parseTableCheck users #[status] #[trimmed, email] source with
      | .ok parsed => pure parsed
      | .error error => panic! s!"PostgreSQL {serverMajor} suffix shape: {error}"
    assert! !parsed.validated
    assert! parsed.source == source
  let ordinary ← match parseTableCheck users #[status] #[trimmed, email]
      "CHECK (age >= 0)" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! ordinary.validated
  let deferredDomain ← match parseDomainCheck trimmed #[status] #[trimmed, email]
      "CHECK (VALUE IS NOT NULL) NOT VALID" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! !deferredDomain.validated
  expectDiagnostic .unsupportedOperator 17
    "NO INHERIT check constraints are unsupported because inheritance metadata is not modeled" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (age >= 0) NO INHERIT"
  expectDiagnostic .unsupportedOperator 17
    "NO INHERIT check constraints are unsupported because inheritance metadata is not modeled" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (age >= 0) NO INHERIT NOT VALID"
  expectDiagnostic .unsupportedOperator 27
    "construct not is not supported after the check expression" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (age >= 0) NOT VALID NOT VALID"
  expectDiagnostic .unsupportedOperator 17
    "construct valid is not supported after the check expression" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (age >= 0) VALID"

  let nullIsNull ← match parseTableCheck users #[status] #[trimmed, email]
      "CHECK (NULL IS NULL)" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! nullIsNull.expression == .constant (some true)
  let nullIsNotNull ← match parseTableCheck users #[status] #[trimmed, email]
      "CHECK (NULL IS NOT NULL)" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! nullIsNotNull.expression == .constant (some false)

  expectDiagnostic .unsupportedType 19
    "pg_catalog.bpchar local constraint semantics are unsupported because fixed-length blank padding is not modeled" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (char_length(code) = 1)"
  expectDiagnostic .unsupportedType 21
    "pg_catalog.bpchar local constraint semantics are unsupported because fixed-length blank padding is not modeled" <|
    parseTableCheck users #[status] #[trimmed, email]
      "CHECK (display_name::bpchar IS NOT NULL)"

  expectDiagnostic .unsafeCast 19
    "cast into domain app.email_address (domain) may enforce a NOT NULL constraint" <|
    parseTableCheck users #[status] #[trimmed, email, checked]
      "CHECK (display_name::app.email_address IS NOT NULL)"
  expectDiagnostic .unsafeCast 19
    "cast into domain app.checked_text (domain) may enforce CHECK constraints" <|
    parseTableCheck users #[status] #[trimmed, email, checked]
      "CHECK (display_name::app.checked_text IS NOT NULL)"
  expectDiagnostic .unsafeCast 9
    "cast into domain app.checked_text (domain) may enforce CHECK constraints" <|
    parseTableCheck users #[status] #[trimmed, email, checked]
      "CHECK (''::app.checked_text IS NOT NULL)"
  expectDiagnostic .unsafeCast 11
    "cast into domain app.email_address (domain) may enforce a NOT NULL constraint" <|
    parseTableCheck users #[status] #[trimmed, email, checked]
      "CHECK (NULL::app.email_address IS NULL)"
  expectDiagnostic .unsafeCast 19
    "cast into domain app.limited_text (domain) may enforce a base type modifier" <|
    parseTableCheck users #[status] #[trimmed, email, checked, limited]
      "CHECK (display_name::app.limited_text IS NOT NULL)"
  expectDiagnostic .unsafeCast 10
    "cast into domain app.wide_int (domain) changes its modeled base type" <|
    parseTableCheck users #[status] #[trimmed, email, checked, wideInt]
      "CHECK (age::app.wide_int IS NOT NULL)"

  let safeDomainWrap ← match parseTableCheck users #[status] #[trimmed, email, checked]
      "CHECK (display_name::app.trimmed_text IS NOT NULL)" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! safeDomainWrap.expression.referencedColumns == #["display_name"]
  let safeDomainUnwrap ← match parseTableCheck users #[status] #[trimmed, email, checked]
      "CHECK (email::text IS NOT NULL)" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! anyValue hasDomainUnwrap safeDomainUnwrap.expression
  let safeCheckedUnwrap ← match
      parseTableCheck users #[status] #[trimmed, email, checked]
        "CHECK (checked_value::text IS NOT NULL)" with
    | .ok parsed => pure parsed
    | .error error => panic! toString error
  assert! anyValue hasDomainUnwrap safeCheckedUnwrap.expression
  expectDiagnostic .unsafeCast 20
    "cast into domain app.checked_text (domain) may enforce CHECK constraints" <|
    parseTableCheck users #[status] #[trimmed, email, checked]
      "CHECK (checked_value::app.checked_text IS NOT NULL)"

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
