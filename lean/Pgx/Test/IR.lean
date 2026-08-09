import Pgx.TypeMapping

open Pgx

private def int4 : TypeRef :=
  { key := { schema := "pg_catalog", name := "int4", kind := .base } }

private def text : TypeRef :=
  { key := { schema := "pg_catalog", name := "text", kind := .base } }

private def status : TypeRef :=
  { key := { schema := "app", name := "status", kind := .enum } }

private def sample : DatabaseIR := {
  serverMajor := 18
  serverFeatures := #["identity-columns", "generated-columns"]
  session := { searchPath := #["app", "pg_catalog"] }
  schemas := #[{ name := "app" }]
  enums := #[{
    key := { schema := "app", name := "status", kind := .enum }
    labels := #["active", "disabled"]
  }]
  domains := #[{
    key := { schema := "app", name := "positive_id", kind := .domain }
    base := int4
    notNull := true
    constraints := #["VALUE > 0", "VALUE < 2147483647"]
  }]
  relations := #[{
    key := { schema := "app", name := "users" }
    kind := .table
    columns := #[
      { name := "id", ordinal := 1, ty := int4, nullable := false },
      { name := "status", ordinal := 2, ty := status, nullable := false }
    ]
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
    params := #[
      { position := 1, name := "id", ty := int4, nullable := false },
      { position := 2, name := "status", ty := status, nullable := false }
    ]
    columns := #[
      {
        name := "id"
        ty := int4
        nullable := false
        origin := some {
          relation := { schema := "app", name := "users" }
          name := "id"
        }
      },
      {
        name := "status"
        ty := status
        nullable := false
        origin := some {
          relation := { schema := "app", name := "users" }
          name := "status"
        }
      }
    ]
    cardinality := .zeroOrOne
  }]
}

private def shuffledFixture : DatabaseIR := {
  sample with
  schemas := sample.schemas.push { name := "audit" }
  enums := sample.enums.push {
    key := { schema := "audit", name := "action", kind := .enum }
    labels := #["insert", "update"]
  }
  domains := sample.domains.push {
    key := { schema := "audit", name := "actor", kind := .domain }
    base := text
    notNull := true
  }
  relations := sample.relations.push {
    key := { schema := "audit", name := "events" }
    kind := .table
    columns := #[{ name := "actor", ordinal := 1, ty := text, nullable := false }]
  }
  constraints := sample.constraints.push {
    relation := { schema := "audit", name := "events" }
    name := "events_actor_not_null"
    kind := .notNull
    columns := #["actor"]
  }
  indexes := #[
    {
      relation := { schema := "app", name := "users" }
      name := "users_id_key"
      unique := true
      primary := false
      valid := true
      columns := #["id"]
    },
    {
      relation := { schema := "audit", name := "events" }
      name := "events_actor_key"
      unique := true
      primary := false
      valid := true
      columns := #["actor"]
    }
  ]
  queries := sample.queries.push {
    name := "ListEvents"
    sql := "select actor from audit.events"
    sqlHash := "def"
    params := #[]
    columns := #[{ name := "actor", ty := text, nullable := false }]
    cardinality := .many
  }
  requiredExtensions := #[("uuid-ossp", "1.1"), ("citext", "1.6")]
  typeOverrides := #[
    {
      key := { schema := "ext", name := "first", kind := .base }
      leanType := "First"
      codec := "firstCodec"
      importModule := some "Ext.First"
    },
    {
      key := { schema := "ext", name := "second", kind := .base }
      leanType := "Second"
      codec := "secondCodec"
    }
  ]
}

private def shuffled (db : DatabaseIR) : DatabaseIR := {
  db with
  serverFeatures := db.serverFeatures.reverse
  schemas := db.schemas.reverse
  enums := db.enums.reverse
  domains := db.domains.reverse.map fun domain =>
    { domain with constraints := domain.constraints.reverse }
  relations := db.relations.reverse.map fun relation =>
    { relation with columns := relation.columns.reverse }
  constraints := db.constraints.reverse
  indexes := db.indexes.reverse
  queries := db.queries.reverse.map fun query =>
    { query with params := query.params.reverse }
  requiredExtensions := db.requiredExtensions.reverse
  typeOverrides := db.typeOverrides.reverse
}

def main : IO UInt32 := do
  assert! sample.contractHash.length == 64
  assert! sample.compatibilityHash.length == 64
  assert! sample.contractHash == sample.contractHash
  assert! (builtinTypeMapping? int4.key).map (·.leanType) == some "Int32"
  assert! (sample.typeSupport? sample.enums[0]!.key).isSome
  let changedQueries := sample.queries.map fun (q : QueryIR) =>
    { q with columns := q.columns.map (fun (c : QueryColumnIR) =>
        { c with nullable := true }) }
  let changed : DatabaseIR := { sample with queries := changedQueries }
  assert! sample.contractHash != changed.contractHash
  let reordered := shuffled shuffledFixture
  assert! shuffledFixture.normalize == reordered.normalize
  assert! shuffledFixture.contractHash == reordered.contractHash
  assert! shuffledFixture.compatibilityHash == reordered.compatibilityHash
  let previousMajor : DatabaseIR := { sample with serverMajor := 17 }
  assert! sample.contractHash != previousMajor.contractHash
  assert! sample.compatibilityHash == previousMajor.compatibilityHash
  let withEmptySchema : DatabaseIR := {
    sample with schemas := sample.schemas.push { name := "empty" }
  }
  assert! sample.contractHash != withEmptySchema.contractHash
  let changedSearchPath : DatabaseIR := {
    sample with session := { sample.session with searchPath := sample.session.searchPath.reverse }
  }
  assert! sample.contractHash != changedSearchPath.contractHash
  let changedEnumOrder : DatabaseIR := {
    sample with enums := sample.enums.map fun value => { value with labels := value.labels.reverse }
  }
  assert! sample.contractHash != changedEnumOrder.contractHash
  let changedColumnOrder : DatabaseIR := {
    sample with queries := sample.queries.map fun query =>
      { query with columns := query.columns.reverse }
  }
  assert! sample.contractHash != changedColumnOrder.contractHash
  let changedOverrideImport : DatabaseIR := {
    shuffledFixture with
    typeOverrides := shuffledFixture.typeOverrides.map fun value =>
      if value.key.name == "first" then
        { value with importModule := some "Ext.First.V2" }
      else value
  }
  assert! shuffledFixture.contractHash != changedOverrideImport.contractHash
  assert! shuffledFixture.compatibilityHash != changedOverrideImport.compatibilityHash
  let oidText := reprStr sample
  assert! !(oidText.contains "tableOid")
  return 0
