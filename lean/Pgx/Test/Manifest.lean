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

private def statusArrayKey : TypeKey := {
  schema := "app", name := "_status", kind := .array
}

private def profileKey : TypeKey := {
  schema := "app", name := "profile", kind := .composite
}

private def int4RangeKey : TypeKey := {
  schema := "pg_catalog", name := "int4range", kind := .range
}

private def int4MultirangeKey : TypeKey := {
  schema := "pg_catalog", name := "int4multirange", kind := .multirange
}

private def relationKey : RelationKey := { schema := "app", name := "users" }

private def positiveId : TypeRef := {
  key := { schema := "app", name := "positive_id", kind := .domain }
}

private def int4Scalar : Constraint.ScalarType := {
  declared := int4
  base := .int32
}

private def idPositive : Constraint.TruthExpr :=
  .compare .gt
    (.column "id" int4Scalar false)
    (.literal (.integer 0) int4Scalar)

private def valuePositive : Constraint.TruthExpr :=
  .compare .gt
    (.domainValue int4Scalar false)
    (.literal (.integer 0) int4Scalar)

private def localQueryConstraint : QueryConstraintIR := {
  relation := relationKey
  name := "users_id_positive"
  source := "CHECK (id > 0)"
  expression := idPositive
}

private def collation : CollationKey := { schema := "pg_catalog", name := "default" }

private def sampleDatabase : DatabaseIR := {
  serverMajor := 18
  supportedServerMajors := #[18, 17]
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
  arrays := #[{ key := statusArrayKey, element := status }]
  domains := #[{
    key := { schema := "app", name := "positive_id", kind := .domain }
    base := int4
    notNull := true
    defaultExpr := some "1"
    constraints := #["VALUE > 0"]
    localConstraints := #[{
      name := "positive_id_check"
      source := "CHECK (VALUE > 0)"
      expression := valuePositive
    }]
  }]
  composites := #[{
    key := profileKey
    fields := #[
      { name := "name", ordinal := 1, ty := { int4 with key := {
          schema := "pg_catalog", name := "text", kind := .base } } },
      { name := "status", ordinal := 2, ty := status, collation := some collation }
    ]
  }]
  ranges := #[{
    key := int4RangeKey
    subtype := int4
    multirange := int4MultirangeKey
    subtypeOpclass := { schema := "pg_catalog", name := "int4_ops" }
    canonical := some {
      schema := "pg_catalog", name := "int4range_canonical"
      inputTypes := #[{ key := int4RangeKey }]
    }
  }]
  multiranges := #[{ key := int4MultirangeKey, range := int4RangeKey }]
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
  views := #[{
    relation := { schema := "app", name := "active_users" }
    definition := " SELECT users.id FROM app.users WHERE users.id > 0;"
    checkOption := .local
    securityBarrier := true
  }]
  routines := #[{
    key := { schema := "app", name := "list_users", inputTypes := #[int4] }
    kind := .function
    args := #[
      { name := some "minimum_id", mode := .input, ty := int4, hasDefault := true },
      { name := some "id", mode := .table, ty := int4 }
    ]
    returnsSet := true
    returnType := some { key := { schema := "pg_catalog", name := "record", kind := .pseudo } }
    resultColumns := #[{ name := "id", ordinal := 1, ty := int4 }]
    strict := true
    volatility := "s"
    parallel := "s"
  }]
  constraints := #[{
    relation := relationKey
    name := "users_pkey"
    kind := .primaryKey
    columns := #["id"]
    validated := true
  }, {
    relation := relationKey
    name := "users_id_positive"
    kind := .check
    columns := #["id"]
    expression := some "CHECK (id > 0)"
    localExpression := some idPositive
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
      logicalType := some positiveId
      nullable := false
      origin := some { relation := relationKey, name := "id" }
      collation := some collation
    }]
    rowPreservedRelations := #[relationKey]
    localConstraints := #[localQueryConstraint]
    cardinality := .zeroOrOne
  }]
  requiredExtensions := #[("citext", "1.6")]
  typeOverrides := #[{
    key := { schema := "ext", name := "vector", kind := .base }
    leanType := "Vector"
    codec := "vectorCodec"
    importModule := some "Ext.Vector"
  }]
  extensionCodecPackages := #[{
    extension := "citext"
    version := "1.6"
    importModule := "Ext.Vector"
    types := #[{ schema := "ext", name := "vector", kind := .base }]
  }]
}

private def validManifest : String :=
  "{" ++
  "\"supportedServerMajors\":[18,17]," ++
  "\"typeOverrides\":[{" ++
    "\"key\":{\"schema\":\"ext\",\"name\":\"vector\",\"kind\":\"base\"}," ++
    "\"leanType\":\"Vector\",\"codec\":\"vectorCodec\"," ++
    "\"importModule\":\"Ext.Vector\"}]," ++
  "\"extensionCodecPackages\":[{" ++
    "\"extension\":\"citext\",\"importModule\":\"Ext.Citext\"," ++
    "\"typeOverrides\":[{" ++
      "\"key\":{\"schema\":\"public\",\"name\":\"citext\",\"kind\":\"base\"}," ++
      "\"leanType\":\"String\",\"codec\":\"citextCodec\"}]}]," ++
  "\"get_user.sql\":{" ++
    "\"leanName\":\"GetUser\"," ++
    "\"cardinality\":\"zeroOrOne\"," ++
    "\"parameters\":[" ++
      "{\"position\":2,\"name\":\"status\",\"nullable\":true}," ++
      "{\"position\":1,\"name\":\"id\",\"nullable\":false}" ++
    "]}" ++
  "}"

private def packagedOverride
    (schema name leanType codec : String) : String :=
  "{\"key\":{\"schema\":\"" ++ schema ++ "\",\"name\":\"" ++ name ++
    "\",\"kind\":\"base\"},\"leanType\":\"" ++ leanType ++
    "\",\"codec\":\"" ++ codec ++ "\"}"

private def codecPackage
    (extension importModule overrides : String) : String :=
  "{\"extension\":\"" ++ extension ++ "\",\"importModule\":\"" ++
    importModule ++ "\",\"typeOverrides\":" ++ overrides ++ "}"

private def packageOnlyDocument (packages : String) : String :=
  "{\"extensionCodecPackages\":" ++ packages ++ "}"

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
  assert! roundTrips (#[(.none : ViewCheckOption), .local, .cascaded])
  assert! roundTrips (#[(.function : RoutineKind), .procedure, .aggregate, .window])
  assert! roundTrips (#[(.input : RoutineArgMode), .output, .inputOutput,
    .variadic, .table])
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
  assert! roundTrips sampleDatabase.arrays[0]!
  assert! roundTrips int4Scalar
  assert! roundTrips idPositive
  assert! roundTrips sampleDatabase.domains[0]!.localConstraints[0]!
  assert! roundTrips sampleDatabase.domains[0]!
  assert! roundTrips sampleDatabase.composites[0]!.fields[0]!
  assert! roundTrips sampleDatabase.composites[0]!
  assert! roundTrips sampleDatabase.ranges[0]!
  assert! roundTrips sampleDatabase.multiranges[0]!
  assert! roundTrips sampleDatabase.relations[0]!.columns[0]!
  assert! roundTrips sampleDatabase.relations[0]!
  assert! roundTrips sampleDatabase.views[0]!
  assert! roundTrips sampleDatabase.routines[0]!.args[0]!
  assert! roundTrips sampleDatabase.routines[0]!.resultColumns[0]!
  assert! roundTrips sampleDatabase.routines[0]!
  assert! roundTrips sampleDatabase.constraints[0]!
  assert! roundTrips sampleDatabase.constraints[1]!
  assert! roundTrips sampleDatabase.indexes[0]!
  assert! roundTrips sampleDatabase.queries[0]!.params[0]!
  assert! roundTrips sampleDatabase.queries[0]!.columns[0]!
  assert! roundTrips sampleDatabase.queries[0]!.localConstraints[0]!
  assert! roundTrips sampleDatabase.queries[0]!
  assert! roundTrips sampleDatabase.session
  assert! roundTrips sampleDatabase.typeOverrides[0]!
  assert! roundTrips sampleDatabase.extensionCodecPackages[0]!
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
  assert! snapshot.contains "\"supportedServerMajors\""
  assert! snapshot.contains "\"logicalType\""
  assert! snapshot.contains "\"nullWidened\""
  assert! snapshot.contains "\"rowPreservedRelations\""
  assert! snapshot.contains "\"localConstraints\""
  assert! snapshot.contains "\"composites\""
  assert! snapshot.contains "\"routines\""
  assert! match DatabaseIR.parseSnapshot snapshot with
    | .ok decoded => decoded == sampleDatabase.normalize
    | .error _ => false
  let legacyDatabase : DatabaseIR := {
    sampleDatabase with supportedServerMajors := #[]
  }
  let legacySnapshot := legacyDatabase.renderSnapshot
  assert! !(legacySnapshot.contains "\"supportedServerMajors\"")
  assert! match DatabaseIR.parseSnapshot legacySnapshot with
    | .ok decoded => decoded.supportedServerMajors.isEmpty &&
        decoded == legacyDatabase.normalize
    | .error _ => false
  let reversed : DatabaseIR := {
    sampleDatabase with serverFeatures := sampleDatabase.serverFeatures.reverse
  }
  assert! reversed.renderSnapshot == sampleDatabase.renderSnapshot
  assert! isError (DatabaseIR.parseSnapshot
    (snapshot.replace "\"formatVersion\": 4" "\"formatVersion\": 99"))

  let manifest ← match Pgx.Codegen.Manifest.parse validManifest with
    | .ok manifest => pure manifest
    | .error error => throw (IO.userError error)
  assert! manifest.supportedServerMajors == #[17, 18]
  assert! manifest.typeOverrides.size == 1
  assert! manifest.typeOverrides[0]!.importModule == some "Ext.Vector"
  assert! manifest.extensionCodecPackages.size == 1
  assert! manifest.requiredExtensionNames == #["citext"]
  assert! manifest.resolvedTypeOverrides.size == 2
  let some packagedCitext := manifest.resolvedTypeOverrides.find? fun override =>
      override.key.name == "citext"
    | throw (IO.userError "resolved package override is missing")
  assert! packagedCitext.importModule == some "Ext.Citext"
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

  -- Package keys are generation configuration, never query basenames.
  let packageOnly ← match Pgx.Codegen.Manifest.parse
      (packageOnlyDocument ("[" ++ codecPackage "citext" "Ext.Citext"
        ("[" ++ packagedOverride "public" "citext" "String" "citextCodec" ++ "]") ++
        "]")) with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! packageOnly.queries.isEmpty
  assert! packageOnly.requiredExtensionNames == #["citext"]

  -- Package and override order is canonical, including the combined view.
  let orderedDocument := packageOnlyDocument <|
    "[" ++
      codecPackage "zeta" "Ext.Zeta"
        ("[" ++ packagedOverride "z" "z_type" "Z" "zCodec" ++ "," ++
          packagedOverride "z" "a_type" "A" "aCodec" ++ "]") ++ "," ++
      codecPackage "alpha" "Ext.Alpha"
        ("[" ++ packagedOverride "a" "only_type" "Only" "onlyCodec" ++ "]") ++
    "]"
  let ordered ← match Pgx.Codegen.Manifest.parse orderedDocument with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! ordered.requiredExtensionNames == #["alpha", "zeta"]
  assert! ordered.codecPackages.map (fun package => package.extension) ==
    #["alpha", "zeta"]
  assert! ordered.codecPackages[1]!.typeOverrides.map (fun override => override.key.name) ==
    #["a_type", "z_type"]
  assert! ordered.resolvedTypeOverrides.map (fun override => override.key.name) ==
    #["only_type", "a_type", "z_type"]
  assert! ordered.resolvedTypeOverrides.all fun override => override.importModule.isSome

  let oneOverride := packagedOverride "public" "citext" "String" "citextCodec"
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "" "Ext.Citext"
      ("[" ++ oneOverride ++ "]") ++ "]")))
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage " citext" "Ext.Citext"
      ("[" ++ oneOverride ++ "]") ++ "]")))
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "citext" ""
      ("[" ++ oneOverride ++ "]") ++ "]")))
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "citext" " Ext.Citext"
      ("[" ++ oneOverride ++ "]") ++ "]")))
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "citext" "Ext.Citext" "[]" ++ "]")))
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "citext" "Ext.Citext"
      ("[" ++ oneOverride.dropEnd 1 ++ ",\"importModule\":\"Other\"}]" ) ++ "]")))

  -- Duplicate extension identities and duplicate PostgreSQL type identities
  -- are rejected within packages, across packages, and against direct entries.
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "citext" "Ext.One"
      ("[" ++ oneOverride ++ "]") ++ "," ++
      codecPackage "citext" "Ext.Two"
        ("[" ++ packagedOverride "public" "other" "Other" "otherCodec" ++ "]") ++
      "]")))
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "citext" "Ext.Citext"
      ("[" ++ oneOverride ++ "," ++ oneOverride ++ "]") ++ "]")))
  assert! isError (Pgx.Codegen.Manifest.parse
    (packageOnlyDocument ("[" ++ codecPackage "citext" "Ext.Citext"
      ("[" ++ oneOverride ++ "]") ++ "," ++ codecPackage "other" "Ext.Other"
      ("[" ++ oneOverride ++ "]") ++ "]")))
  let directCollision :=
    "{\"typeOverrides\":[" ++ oneOverride ++ "],\"extensionCodecPackages\":[" ++
      codecPackage "citext" "Ext.Citext" ("[" ++ oneOverride ++ "]") ++ "]}"
  assert! isError (Pgx.Codegen.Manifest.parse directCollision)
  return 0

end Pgx.Test.Manifest

def main : IO UInt32 := Pgx.Test.Manifest.main
