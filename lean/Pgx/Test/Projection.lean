import Pgx.Codegen.Projection

namespace Pgx.Test.Projection

open Pgx
open Pgx.Constraint

private def int4 : TypeRef := {
  key := { schema := "pg_catalog", name := "int4", kind := .base }
}

private def text : TypeRef := {
  key := { schema := "pg_catalog", name := "text", kind := .base }
}

private def emailDomain : TypeRef := {
  key := { schema := "app", name := "email_address", kind := .domain }
}

private def int4Scalar : ScalarType := { declared := int4, base := .int32 }
private def emailScalar : ScalarType := {
  declared := emailDomain
  base := .text
  domains := #[emailDomain.key]
}

private def usersKey : RelationKey := { schema := "app", name := "users" }
private def otherKey : RelationKey := { schema := "app", name := "other" }

private def users : RelationIR := {
  key := usersKey
  kind := .table
  columns := #[
    { name := "age", ordinal := 1, ty := int4, nullable := false },
    { name := "quota", ordinal := 2, ty := int4, nullable := true },
    { name := "email", ordinal := 3, ty := emailDomain, nullable := false }
  ]
}

private def other : RelationIR := {
  key := otherKey
  kind := .table
  columns := #[
    { name := "age", ordinal := 1, ty := int4, nullable := false }
  ]
}

private def intColumn (name : String) (nullable : Bool) : ValueExpr :=
  .column name int4Scalar nullable

private def zero : ValueExpr := .literal (.integer 0) int4Scalar

private def multiCheckExpr (ageName quotaName : String)
    (ageNullable quotaNullable : Bool) : TruthExpr :=
  .and
    (.compare .ge (intColumn ageName ageNullable) zero)
    (.compare .le (intColumn quotaName quotaNullable)
      (intColumn ageName ageNullable))

private def domainCheckExpr (name : String) (nullable : Bool) : TruthExpr :=
  .compare .ne (.column name emailScalar nullable)
    (.literal (.text "") { declared := text, base := .text })

private def constraint (name source : String) (expression : TruthExpr)
    (validated : Bool := true) : ConstraintIR := {
  relation := usersKey
  name
  kind := .check
  expression := some source
  localExpression := some expression
  validated
}

private def query (columns : Array QueryColumnIR) : QueryIR := {
  name := "ProjectionFixture"
  sql := "SELECT fixture"
  sqlHash := "fixture"
  params := #[]
  columns
  cardinality := .many
}

private def origin (relation : RelationKey) (name : String) : Option ColumnKey :=
  some { relation, name }

private def resultColumn (name : String) (ty : TypeRef) (nullable : Bool)
    (columnOrigin : Option ColumnKey) (logicalType : Option TypeRef := none) :
    QueryColumnIR := {
  name
  ty
  logicalType
  nullable
  origin := columnOrigin
}

private def project (constraints : Array ConstraintIR) (value : QueryIR) :
    Array QueryConstraintIR :=
  Pgx.Codegen.Projection.localConstraints #[users, other] constraints value

private def multi : ConstraintIR :=
  constraint "users_age_quota" "CHECK (age >= 0 AND quota <= age)"
    (multiCheckExpr "age" "quota" false true)

def main : IO UInt32 := do
  let completeQuery := query #[
    resultColumn "years" int4 false (origin usersKey "age"),
    resultColumn "limit" int4 true (origin usersKey "quota")
  ]
  let complete := project #[multi] completeQuery
  assert! complete.size == 1
  assert! complete[0]!.relation == usersKey
  assert! complete[0]!.name == "users_age_quota"
  assert! complete[0]!.expression == multiCheckExpr "years" "limit" false true
  assert! complete[0]!.expression.referencedColumns == #["years", "limit", "years"]

  -- Every referenced source field must be projected.
  let incomplete := project #[multi] <| query #[
    resultColumn "years" int4 false (origin usersKey "age")
  ]
  assert! incomplete.isEmpty

  -- Aliases are rewritten from explicit origin metadata.
  let aliasOnly := constraint "users_age" "CHECK (age >= 0)"
    (.compare .ge (intColumn "age" false) zero)
  let aliased := project #[aliasOnly] <| query #[
    resultColumn "renamed_age" int4 false (origin usersKey "age")
  ]
  assert! aliased.size == 1
  assert! aliased[0]!.expression.referencedColumns == #["renamed_age"]

  -- A matching result name/type from another relation is not provenance.
  let wrongOrigin := project #[aliasOnly] <| query #[
    resultColumn "age" int4 false (origin otherKey "age")
  ]
  assert! wrongOrigin.isEmpty

  -- Casts and expressions described without a table origin do not propagate.
  let expressionResult := project #[aliasOnly] <| query #[
    resultColumn "age" int4 false none
  ]
  assert! expressionResult.isEmpty

  -- Ambiguous duplicate projections are rejected rather than selected by order.
  let duplicateOrigin := project #[aliasOnly] <| query #[
    resultColumn "age_one" int4 false (origin usersKey "age"),
    resultColumn "age_two" int4 false (origin usersKey "age")
  ]
  assert! duplicateOrigin.isEmpty

  -- A nullable outer-join result must not inherit a non-null source check.
  let widenedNull := project #[aliasOnly] <| query #[
    resultColumn "age" int4 true (origin usersKey "age")
  ]
  assert! widenedNull.isEmpty

  -- A domain may travel over its base wire type only with an explicit logical
  -- type proving that the direct result still represents the domain column.
  let domainConstraint := constraint "users_email" "CHECK (email <> '')"
    (domainCheckExpr "email" false)
  let logicalDomain := project #[domainConstraint] <| query #[
    resultColumn "address" text false (origin usersKey "email") (some emailDomain)
  ]
  assert! logicalDomain.size == 1
  assert! logicalDomain[0]!.expression == domainCheckExpr "address" false
  let wireOnly := project #[domainConstraint] <| query #[
    resultColumn "address" text false (origin usersKey "email")
  ]
  assert! wireOnly.isEmpty

  -- NOT VALID is catalog history, not permission to manufacture a proof.
  -- It remains attached so decoding locally rejects any legacy bad row.
  let notValidated := constraint "users_age_legacy" "CHECK (age >= 0) NOT VALID"
    (.compare .ge (intColumn "age" false) zero) false
  let retainedLegacy := project #[notValidated] <| query #[
    resultColumn "age" int4 false (origin usersKey "age")
  ]
  assert! retainedLegacy.size == 1
  assert! !retainedLegacy[0]!.validated

  -- A no-column check can follow a relation only when some valid direct
  -- projection establishes that the relation participates in the result.
  let constant := constraint "users_constant" "CHECK (true)"
    (.constant (some Bool.true))
  assert! (project #[constant] <| query #[
    resultColumn "age" int4 false (origin usersKey "age")
  ]).size == 1
  assert! (project #[constant] <| query #[
    resultColumn "age" int4 false (origin otherKey "age")
  ]).isEmpty

  -- Only typed local CHECK expressions participate.
  let relational : ConstraintIR := {
    notValidated with kind := .unique, validated := true
  }
  assert! (project #[relational] completeQuery).isEmpty
  assert! (project #[{ aliasOnly with localExpression := none }] completeQuery).isEmpty

  let planned := Pgx.Codegen.Projection.planQuery #[users, other] #[multi] completeQuery
  assert! planned.localConstraints == complete
  return 0

end Pgx.Test.Projection

def main : IO UInt32 := Pgx.Test.Projection.main
