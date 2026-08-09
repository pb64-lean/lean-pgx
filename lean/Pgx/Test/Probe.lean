import Pgx.Codegen.Probe

namespace Pgx.Test.Probe

open Pgx.Codegen.Probe

private def validConfig : Config := {
  schemas := #["app"]
  session := { searchPath := #["app", "pg_catalog"] }
  supportedServerMajors := #[18, 17]
  queries := #[{
    name := "GetUser"
    sql := "SELECT id FROM app.users WHERE id = $1"
    cardinality := .zeroOrOne
    parameters := #[{ position := 1, name := "id", nullable := false }]
  }]
}

private def isError : Except Error α → Bool
  | .error _ => true
  | .ok _ => false

private def relation : Pgx.RelationKey := { schema := "app", name := "users" }

private def commonConstraint : Pgx.ConstraintIR := {
  relation
  name := "users_pkey"
  kind := .primaryKey
  columns := #["id"]
}

private def nativeNotNull : Pgx.ConstraintIR := {
  relation
  name := "users_email_required"
  kind := .notNull
  columns := #["email"]
}

private def attributeNotNull : Array AttributeNotNull := #[
  { relation, column := "email" },
  { relation, column := "id" }
]

private def innerPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Hash Join\",\"Join Type\":\"Inner\"," ++
  "\"Plans\":[{\"Node Type\":\"Seq Scan\"},{\"Node Type\":\"Hash\"," ++
  "\"Plans\":[{\"Node Type\":\"Index Scan\"}]}]}}]"

private def leftPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Nested Loop\",\"Join Type\":\"Left\"," ++
  "\"Plans\":[{\"Node Type\":\"Seq Scan\"},{\"Node Type\":\"Index Scan\"}]}}]"

private def fullPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Aggregate\",\"Plans\":[{" ++
  "\"Node Type\":\"Merge Join\",\"Join Type\":\"Full\"," ++
  "\"Plans\":[{\"Node Type\":\"Sort\"},{\"Node Type\":\"Sort\"}]}]}}]"

def main : IO UInt32 := do
  assert! (validateConfig validConfig).isOk
  assert! validConfig.normalizedSupportedServerMajors == #[17, 18]
  assert! (adapterForServerMajor? 17).map (·.serverMajor) == some 17
  assert! (adapterForServerMajor? 18).map (·.serverMajor) == some 18
  assert! (adapterForServerMajor? 16).isNone
  assert! !Pg17.adapter.supportsNativeNotNull
  assert! Pg18.adapter.supportsNativeNotNull
  assert! !Pg17.adapter.constraintTypeTags.contains "n"
  assert! Pg18.adapter.constraintTypeTags.contains "n"
  let normalized17 := Pg17.adapter.normalizeConstraints
    #[commonConstraint] attributeNotNull
  let normalized18 := Pg18.adapter.normalizeConstraints
    #[commonConstraint, nativeNotNull] attributeNotNull
  let constraints17 ← match normalized17 with
    | .error message => panic! message
    | .ok constraints => pure constraints
  let constraints18 ← match normalized18 with
    | .error message => panic! message
    | .ok constraints => pure constraints
  assert! constraints17 == constraints18
  let some email := constraints18.find? fun (constraint : Pgx.ConstraintIR) =>
      constraint.kind == .notNull && constraint.columns == #["email"]
    | panic! "normalized email NOT NULL constraint is missing"
  assert! email.name == "<not-null:email>"
  match Pg17.adapter.normalizeConstraints
      #[commonConstraint, nativeNotNull] attributeNotNull with
  | .error _ => pure ()
  | .ok _ => panic! "PostgreSQL 17 accepted a native NOT NULL catalog row"
  match Pg18.adapter.normalizeConstraints #[nativeNotNull] #[] with
  | .error _ => pure ()
  | .ok _ => panic! "PostgreSQL 18 accepted a native NOT NULL row missing from pg_attribute"
  assert! isError (validateConfig { validConfig with schemas := #["app", "app"] })
  assert! isError (validateConfig { validConfig with schemas := #[""] })
  assert! isError (validateConfig {
    validConfig with supportedServerMajors := #[17, 18, 19]
  })
  let sparse := validConfig.queries.map fun query => {
    query with parameters := #[
      { position := 1, name := "first", nullable := false },
      { position := 3, name := "third", nullable := true }
    ]
  }
  assert! isError (validateConfig { validConfig with queries := sparse })
  let emptySql := validConfig.queries.map fun query => { query with sql := " \n\t" }
  assert! isError (validateConfig { validConfig with queries := emptySql })

  assert! analyzeOuterJoinPlanJson innerPlan == .noOuterJoin
  assert! analyzeOuterJoinPlanJson leftPlan == .outerJoin
  assert! analyzeOuterJoinPlanJson fullPlan == .outerJoin
  assert! analyzeOuterJoinPlanJson
    "[{\"Plan\":{\"Node Type\":\"Future Scan\"}}]" == .uncertain
  assert! analyzeOuterJoinPlanJson
    "{\"unexpected\":{\"Node Type\":\"Seq Scan\"}}" == .uncertain
  assert! analyzeOuterJoinPlanJson
    "[{\"Plan\":{\"Node Type\":\"Seq Scan\"}" == .uncertain
  return 0

end Pgx.Test.Probe

def main : IO UInt32 := Pgx.Test.Probe.main
