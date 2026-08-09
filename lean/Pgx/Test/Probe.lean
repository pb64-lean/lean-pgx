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
  assert! isError (validateConfig { validConfig with schemas := #["app", "app"] })
  assert! isError (validateConfig { validConfig with schemas := #[""] })
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
