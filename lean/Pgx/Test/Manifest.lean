import Pgx.Codegen.Manifest

namespace Pgx.Test.Manifest

open Lean
open Pgx
open Pgx.Codegen

private def roundTrips [BEq α] [ToJson α] [FromJson α] (value : α) : Bool :=
  match fromJson? (toJson value) with
  | .ok decoded => decoded == value
  | .error _ => false

private def isError : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def int4 : TypeRef := {
  key := { schema := "pg_catalog", name := "int4", kind := .base }
  typmod := some (Int32.ofInt (-1))
}

private def status : TypeRef := {
  key := { schema := "app", name := "status", kind := .enum }
}

private def relationKey : RelationKey := { schema := "app", name := "users" }

private def collation : CollationKey := { schema := "pg_catalog", name := "default" }

private def sampleDatabase : DatabaseIR := {
  serverMajor := 18
  serverFeatures := #["generated-columns", "identity-columns"]
  session := {
    searchPath := #["app", "pg_catalog"]
    timezone := "UTC"
    encoding := "UTF8"
    standardConformingStrings := true
  }
  schemas := #[{ name := "app" }]
  enums := #[{
    key := status.key
    labels := #["active", "disabled"]
  }]
  domains := #[{
    key := { schema := "app", name := "positive_id", kind := .domain }
    base := int4
    notNull := true
    defaultExpr := some "1"
    constraints := #["VALUE > 0"]
  }]
  relations := #[{
    key := relationKey
    kind := .table
    columns := #[{
      name := "id"
      ordinal := 1
      ty := int4
      nullable := false
      identity := true
      defaultExpr := some "nextval('users_id_seq')"
      collation := some collation
    }]
  }]
  constraints := #[{
    relation := relationKey
    name := "users_pkey"
    kind := .primaryKey
    columns := #["id"]
    validated := true
  }]
  indexes := #[{
    relation := relationKey
    name := "users_pkey"
    unique := true
    primary := true
    valid := true
    columns := #["id"]
  }]
  queries := #[{
    name := "GetUser"
    sql := "select id, status from app.users where id = $1"
    sqlHash := "0123456789abcdef"
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
      origin := some { relation := relationKey, name := "id" }
      collation := some collation
    }]
    cardinality := .zeroOrOne
  }]
  requiredExtensions := #[("citext", "1.6")]
  typeOverrides := #[{
    key := { schema := "ext", name := "vector", kind := .base }
    leanType := "Vector"
    codec := "vectorCodec"
    importModule := some "Ext.Vector"
  }]
}

private def validManifest : String :=
  "{" ++
  "\"supportedServerMajors\":[18,17]," ++
  "\"typeOverrides\":[{" ++
    "\"key\":{\"schema\":\"ext\",\"name\":\"vector\",\"kind\":\"base\"}," ++
    "\"leanType\":\"Vector\",\"codec\":\"vectorCodec\"," ++
    "\"importModule\":\"Ext.Vector\"}]," ++
  "\"get_user.sql\":{" ++
    "\"leanName\":\"GetUser\"," ++
    "\"cardinality\":\"zeroOrOne\"," ++
    "\"parameters\":[" ++
      "{\"position\":2,\"name\":\"status\",\"nullable\":true}," ++
      "{\"position\":1,\"name\":\"id\",\"nullable\":false}" ++
    "]}" ++
  "}"

private def queryDocument
    (leanName cardinality parameters : String) : String :=
  "{\"get_user.sql\":{" ++
    "\"leanName\":\"" ++ leanName ++ "\"," ++
    "\"cardinality\":\"" ++ cardinality ++ "\"," ++
    "\"parameters\":" ++ parameters ++
  "}}"

def main : IO UInt32 := do
  -- Every IR enum encoding is a stable string tag.
  assert! roundTrips (#[(.base : TypeKind), .enum, .domain, .array, .range,
    .multirange, .composite, .pseudo])
  assert! roundTrips (#[(.table : RelationKind), .partitionedTable, .view,
    .materializedView, .foreignTable])
  assert! roundTrips (#[(.check : ConstraintKind), .notNull, .primaryKey,
    .unique, .foreignKey, .exclusion])
  assert! roundTrips (#[(.execute : Cardinality), .exactlyOne, .zeroOrOne, .many])

  -- Representative values cover every structure codec in Pgx.IR.Json.
  assert! roundTrips int4.key
  assert! roundTrips int4
  assert! roundTrips relationKey
  assert! roundTrips ({ relation := relationKey, name := "id" } : ColumnKey)
  assert! roundTrips collation
  assert! roundTrips sampleDatabase.schemas[0]!
  assert! roundTrips sampleDatabase.enums[0]!
  assert! roundTrips sampleDatabase.domains[0]!
  assert! roundTrips sampleDatabase.relations[0]!.columns[0]!
  assert! roundTrips sampleDatabase.relations[0]!
  assert! roundTrips sampleDatabase.constraints[0]!
  assert! roundTrips sampleDatabase.indexes[0]!
  assert! roundTrips sampleDatabase.queries[0]!.params[0]!
  assert! roundTrips sampleDatabase.queries[0]!.columns[0]!
  assert! roundTrips sampleDatabase.queries[0]!
  assert! roundTrips sampleDatabase.session
  assert! roundTrips sampleDatabase.typeOverrides[0]!
  let legacyOverrideJson ← match Json.parse
      ("{\"key\":{\"schema\":\"ext\",\"name\":\"legacy\",\"kind\":\"base\"}," ++
        "\"leanType\":\"Legacy\",\"codec\":\"legacyCodec\"}") with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let legacyOverride ← match
      (fromJson? legacyOverrideJson : Except String TypeOverrideIR) with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! legacyOverride.importModule.isNone
  assert! !((toJson legacyOverride).compress.contains "importModule")

  let snapshot := sampleDatabase.renderSnapshot
  assert! snapshot == sampleDatabase.renderSnapshot
  assert! match DatabaseIR.parseSnapshot snapshot with
    | .ok decoded => decoded == sampleDatabase.normalize
    | .error _ => false
  let reversed : DatabaseIR := {
    sampleDatabase with serverFeatures := sampleDatabase.serverFeatures.reverse
  }
  assert! reversed.renderSnapshot == sampleDatabase.renderSnapshot
  assert! isError (DatabaseIR.parseSnapshot
    (snapshot.replace "\"formatVersion\": 1" "\"formatVersion\": 2"))

  let manifest ← match Pgx.Codegen.Manifest.parse validManifest with
    | .ok manifest => pure manifest
    | .error error => throw (IO.userError error)
  assert! manifest.supportedServerMajors == #[17, 18]
  assert! manifest.typeOverrides.size == 1
  assert! manifest.typeOverrides[0]!.importModule == some "Ext.Vector"
  assert! manifest.queries.size == 1
  let query := manifest.queries[0]!
  assert! query.sqlBasename == "get_user.sql"
  assert! query.leanName == "GetUser"
  assert! query.parameters.map (fun (parameter : ManifestParameter) => parameter.position) == #[1, 2]
  assert! (Pgx.Codegen.Manifest.queryForFile? manifest "queries/get_user.sql").isSome
  assert! (Pgx.Codegen.Manifest.validateQueryFiles manifest
    #["queries/get_user.sql"]).isOk
  assert! isError (Pgx.Codegen.Manifest.validateQueryFiles manifest
    #["queries/other.sql"])

  for cardinality in #["execute", "exactlyOne", "zeroOrOne", "many"] do
    assert! (Pgx.Codegen.Manifest.parse
      (queryDocument "GetUser" cardinality "[]")).isOk

  assert! isError (Pgx.Codegen.Manifest.parse
    (queryDocument "WrongName" "many" "[]"))
  assert! isError (Pgx.Codegen.Manifest.parse
    (queryDocument "GetUser" "atMostTwo" "[]"))
  assert! isError (Pgx.Codegen.Manifest.parse
    (queryDocument "GetUser" "many"
      "[{\"position\":2,\"name\":\"id\",\"nullable\":false}]"))
  assert! isError (Pgx.Codegen.Manifest.parse
    (queryDocument "GetUser" "many"
      "[{\"position\":1,\"name\":\"\",\"nullable\":false}]"))
  assert! isError (Pgx.Codegen.Manifest.parse
    (queryDocument "GetUser" "many"
      "[{\"position\":1,\"name\":\"id\",\"nullable\":false}," ++
      "{\"position\":2,\"name\":\"id\",\"nullable\":true}]"))
  assert! isError (Pgx.Codegen.Manifest.parse
    ("{\"queries/get_user.sql\":{" ++
      "\"leanName\":\"GetUser\",\"cardinality\":\"many\",\"parameters\":[]}}"))
  assert! isError (Pgx.Codegen.Manifest.parse
    (validManifest.replace "Ext.Vector" " Ext.Vector"))
  assert! isError (Pgx.Codegen.Manifest.parse
    (validManifest.replace "Ext.Vector" ""))
  return 0

end Pgx.Test.Manifest

def main : IO UInt32 := Pgx.Test.Manifest.main
