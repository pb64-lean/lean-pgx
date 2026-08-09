import Pgx.TypeMapping

open Pgx

private def int4 : TypeRef :=
  { key := { schema := "pg_catalog", name := "int4", kind := .base } }

private def sample : DatabaseIR := {
  serverMajor := 18
  session := { searchPath := #["app", "pg_catalog"] }
  schemas := #[{ name := "app" }]
  enums := #[{
    key := { schema := "app", name := "status", kind := .enum }
    labels := #["active", "disabled"]
  }]
  domains := #[]
  relations := #[{
    key := { schema := "app", name := "users" }
    kind := .table
    columns := #[{ name := "id", ordinal := 1, ty := int4, nullable := false }]
  }]
  constraints := #[{
    relation := { schema := "app", name := "users" }
    name := "users_pkey"
    kind := .primaryKey
    columns := #["id"]
  }]
  indexes := #[]
  queries := #[{
    name := "GetUser"
    sql := "select id from app.users where id = $1"
    sqlHash := "abc"
    params := #[{ position := 1, name := "id", ty := int4, nullable := false }]
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
  assert! sample.contractHash.length == 64
  assert! sample.contractHash == sample.contractHash
  assert! (builtinTypeMapping? int4.key).map (·.leanType) == some "Int32"
  assert! (sample.typeSupport? sample.enums[0]!.key).isSome
  let changedQueries := sample.queries.map fun (q : QueryIR) =>
    { q with columns := q.columns.map (fun (c : QueryColumnIR) =>
        { c with nullable := true }) }
  let changed : DatabaseIR := { sample with queries := changedQueries }
  assert! sample.contractHash != changed.contractHash
  let oidText := reprStr sample
  assert! !(oidText.contains "tableOid")
  return 0
