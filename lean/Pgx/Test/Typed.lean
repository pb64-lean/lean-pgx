import Pgx.Typed.Catalog

open Pgx.Typed

private def int4Key : Pgx.TypeKey :=
  { schema := "pg_catalog", name := "int4", kind := .base }

private def textKey : Pgx.TypeKey :=
  { schema := "pg_catalog", name := "text", kind := .base }

private def int4 : Pgx.TypeRef := { key := int4Key, typmod := some (-1) }
private def text : Pgx.TypeRef := { key := textKey, typmod := some (-1) }

private def usersKey : Pgx.RelationKey := { schema := "app", name := "users" }

private def int4Desc : StaticTypeDesc := { key := int4Key }
private def textDesc : StaticTypeDesc := { key := textKey }

private def activeUsersKey : Pgx.RelationKey :=
  { schema := "app", name := "active_users" }

private def activeUsersView : Pgx.ViewIR := {
  relation := activeUsersKey
  definition := "SELECT id FROM app.users WHERE active"
  checkOption := .local
  securityBarrier := true
}

private def lookupRoutine : Pgx.RoutineIR := {
  key := { schema := "app", name := "lookup_user", inputTypes := #[int4] }
  kind := .function
  args := #[{ name := some "id", mode := .input, ty := int4 }]
  returnsSet := false
  returnType := some text
  strict := true
  volatility := "s"
  parallel := "s"
}

private def resolveTestType : TypeResolver
  | key =>
      if key == int4Key then
        pure { expected := int4Desc, oid := 23 }
      else if key == textKey then
        pure { expected := textDesc, oid := 25 }
      else
        throw (.unsupportedType key)

private def int4Codec : ResolvedCodec Int32 where
  expected := int4Desc
  encode _ resolved value := do
    unless resolved.expected == int4Desc && resolved.oid == 23 do
      throw (.schemaDrift "int4 codec received the wrong resolved descriptor")
    pure { format := 0, value := some (toString value).toUTF8 }
  decode _ resolved format value :=
    match Pg.decodeValue (α := Int32) resolved.oid format value with
    | .ok decoded => pure decoded
    | .error message => throw (.decode message)

private def binaryInt4Codec : ResolvedCodec Int32 where
  expected := int4Desc
  encode _ _ _ := pure { format := 1, value := some (ByteArray.mk #[0, 0, 0, 42]) }
  decode _ resolved format value :=
    match Pg.decodeValue (α := Int32) resolved.oid format value with
    | .ok decoded => pure decoded
    | .error message => throw (.decode message)

private def idColumn : StaticColumnDesc :=
  { name := "id", ordinal := 1, ty := int4, nullable := false }

private def emailColumn : StaticColumnDesc :=
  { name := "email", ordinal := 2, ty := text, nullable := false }

private def users : StaticRelationDesc := {
  key := usersKey
  kind := .table
  columns := #[idColumn, emailColumn]
}

private def database : DatabaseDesc := {
  canonicalMajor := 18
  serverMajors := #[17, 18]
  session := { searchPath := #["app", "pg_catalog"] }
  types := #[int4Desc, textDesc]
  relations := #[users]
  schemaHash := "schema"
  contractHash := "contract"
}

private def catalogResult : Except Error (ResolvedCatalog database) :=
  ResolvedCatalog.create database
    #[
      { expected := int4Desc, oid := 23 },
      { expected := textDesc, oid := 25 }
    ]
    #[{
      expected := users
      oid := 90001
      columns := #[
        { expected := idColumn, attnum := 1 },
        { expected := emailColumn, attnum := 2 }
      ]
    }]

private def idResult : Pg.Protocol.ColumnDesc := {
  name := "id"
  tableOid := 90001
  attnum := 1
  typeOid := 23
  typeSize := 4
  typeMod := -1
  format := 0
}

private def statement : Pg.Statement := {
  name := "get_user"
  paramTypes := #[23]
  columns := #[idResult]
}

private def param : ParamSpec := { name := "id", ty := int4, nullable := false }

private def column : ColumnSpec := {
  name := "id"
  ty := int4
  nullable := false
  origin := some { relation := usersKey, name := "id" }
}

private def failed (result : Except Error Unit) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def okEq [BEq α] (result : Except Error α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def isError (result : Except Error α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def resolvedCodecTests : IO Unit := do
  let binary42 := ByteArray.mk #[0, 0, 0, 42]
  assert! okEq (int4Codec.encodeText resolveTestType int4 42) "42"
  assert! okEq (int4Codec.decodeText resolveTestType int4 "-17") (-17)
  assert! okEq (int4Codec.decodeBinary resolveTestType int4 23 binary42) 42

  -- The enclosing container's OID and the codec's symbolic descriptor are
  -- both checked before any component decoder can observe the payload.
  assert! isError (int4Codec.decodeBinary resolveTestType int4 25 binary42)
  assert! isError (int4Codec.encodeText resolveTestType text 42)
  assert! isError (int4Codec.decodeText resolveTestType text "42")

  -- Binary-only extension codecs cannot silently reinterpret their bytes as
  -- a PostgreSQL container's text representation.
  assert! isError (binaryInt4Codec.encodeText resolveTestType int4 42)

  let optional := int4Codec.option
  assert! okEq (optional.encode resolveTestType
    { expected := int4Desc, oid := 23 } none)
      ({ format := 0, value := none } : EncodedValue)
  assert! okEq (optional.decode resolveTestType
    { expected := int4Desc, oid := 23 } 1 none) none

private def semanticMetadataTests : IO Unit := do
  assert! (validateViewMetadata #[activeUsersView] #[activeUsersView]).isOk
  assert! isError (validateViewMetadata #[activeUsersView]
    #[{ activeUsersView with definition := "SELECT id FROM app.users" }])
  assert! isError (validateViewMetadata #[activeUsersView]
    #[activeUsersView, activeUsersView])

  assert! (validateRoutineMetadata #[lookupRoutine] #[lookupRoutine]).isOk
  assert! isError (validateRoutineMetadata #[lookupRoutine]
    #[{ lookupRoutine with strict := false }])
  assert! isError (validateRoutineMetadata #[lookupRoutine] #[])

  let extensionKey : Pgx.TypeKey :=
    { schema := "ext", name := "citext", kind := .base }
  let extensionDb : DatabaseDesc := {
    database with
    types := database.types.push { key := extensionKey }
    requiredExtensions := #[("citext", "1.6")]
    extensionCodecPackages := #[{
      extension := "citext"
      version := "1.6"
      importModule := "Pg.Types.Citext"
      types := #[extensionKey]
    }]
  }
  assert! (validateExtensionMetadata extensionDb
    #[("citext", "1.6"), ("plpgsql", "1.0")]).isOk
  assert! isError (validateExtensionMetadata extensionDb #[("citext", "1.5")])
  assert! isError (validateExtensionMetadata extensionDb #[])
  assert! isError (validateExtensionMetadata {
    extensionDb with
    extensionCodecPackages := extensionDb.extensionCodecPackages.map fun package =>
      { package with version := "1.5" }
  } #[("citext", "1.6")])
  assert! isError (validateExtensionMetadata {
    extensionDb with types := database.types
  } #[("citext", "1.6")])

def main : IO UInt32 := do
  resolvedCodecTests
  semanticMetadataTests
  let catalog ← match catalogResult with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  assert! (verifyStatement catalog #[param] #[column] statement).isOk
  assert! failed (verifyStatement catalog #[] #[column] statement)
  assert! failed (verifyStatement catalog #[param] #[column]
    { statement with paramTypes := #[25] })
  assert! failed (verifyStatement catalog #[param] #[column]
    { statement with columns := #[{ idResult with name := "user_id" }] })
  assert! failed (verifyStatement catalog #[param] #[column]
    { statement with columns := #[{ idResult with typeOid := 25 }] })
  assert! failed (verifyStatement catalog #[param] #[column]
    { statement with columns := #[{ idResult with typeMod := 42 }] })
  let columnWithoutTypmod : ColumnSpec := { column with ty := { int4 with typmod := none } }
  assert! (verifyStatement catalog #[param] #[columnWithoutTypmod] statement).isOk
  assert! failed (verifyStatement catalog #[param] #[columnWithoutTypmod]
    { statement with columns := #[{ idResult with typeMod := 42 }] })
  assert! failed (verifyStatement catalog #[param] #[column]
    { statement with columns := #[{ idResult with tableOid := 90002 }] })
  assert! okEq (decodeBuiltin (α := Int32) catalog int4 0 (some "42".toUTF8)) 42
  assert! okEq (decodeBuiltin (α := Option Int32) catalog int4 0 none) none
  assert! isError (decodeBuiltin (α := Int32) catalog int4 0 none)
  let encoded ← match encodeBuiltin catalog int4 (42 : Int32) with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  assert! encoded.format == 0
  assert! encoded.value == some "42".toUTF8
  assert! toString (Error.constraintViolation
    (.checkFailed "users_display_name_not_blank")) ==
      "local constraint violation: PostgreSQL check users_display_name_not_blank evaluated to false"
  return 0
