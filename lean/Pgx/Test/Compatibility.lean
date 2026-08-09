import Pgx.IR.Json

open Pgx

private def int4 : TypeRef := {
  key := { schema := "pg_catalog", name := "int4", kind := .base }
}

private def database (serverMajor : Nat) : DatabaseIR := {
  serverMajor
  supportedServerMajors := #[17, 18]
  session := { searchPath := #["app", "pg_catalog"] }
  schemas := #[{ name := "app" }]
  enums := #[]
  domains := #[]
  relations := #[{
    key := { schema := "app", name := "users" }
    kind := .table
    columns := #[{
      name := "id"
      ordinal := 1
      ty := int4
      nullable := false
    }]
  }]
  constraints := #[]
  indexes := #[]
  queries := #[{
    name := "GetUser"
    sql := "select id from app.users where id = $1"
    sqlHash := "query-hash"
    params := #[{
      position := 1
      name := "id"
      ty := int4
      nullable := false
    }]
    columns := #[{
      name := "id"
      ty := int4
      nullable := false
      origin := some {
        relation := { schema := "app", name := "users" }
        name := "id"
      }
    }]
    cardinality := .zeroOrOne
  }]
}

def main : IO UInt32 := do
  let pg17 := database 17
  let pg18 := database 18
  -- The ordinary contract fingerprints the canonical server major.
  assert! pg17.contractHash != pg18.contractHash
  -- Compatibility deliberately ignores only that major difference.
  assert! pg17.compatibilityHash == pg18.compatibilityHash

  let driftedQueries := pg18.queries.map fun query => {
    query with columns := query.columns.map fun column => {
      column with nullable := true
    }
  }
  let drifted : DatabaseIR := { pg18 with queries := driftedQueries }
  assert! pg17.compatibilityHash != drifted.compatibilityHash
  return 0
