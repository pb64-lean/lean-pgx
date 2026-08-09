import Pgx.Typed.Descriptors

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

def main : IO UInt32 := do
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
  return 0
