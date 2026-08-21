import Pgx.Typed.Catalog

open Pgx.Typed
open Pgx.Typed.Internal

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

private structure SpanProbe where
  ownerSize : Nat
  offset : Nat
  length : Nat
  deriving Repr, BEq

private instance : Pg.PgDecode SpanProbe where
  decodeText _ _ := throw "span probe requires binary input"
  decodeBinary _ _ := throw "span probe must not receive a materialized cell"

private instance : Pg.PgDecodeSpan SpanProbe where
  decodeBinarySpan _ owner offset length :=
    pure { ownerSize := owner.size, offset, length }

private def echoCodec : ResolvedCodec ByteArray where
  expected := int4Desc
  encode _ _ value := pure { format := 1, value := some value }
  decode _ _ _
    | some value => pure value
    | none => throw (.decode "echo codec received NULL")

/-- Exercise the ownership escape through the prepared built-in descriptor:
the decoded value is the exact borrowed result-cell payload. -/
@[noinline] private def decodeOwnedPlannedBytea
    (value : Option ByteArray) : Except Error ByteArray :=
  decodePlannedBuiltin Pg.Oid.bytea 1 value

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

/-- An old-form manual spec: prepared callbacks may be supplied without opting
into the additive row-span decoder. -/
private def legacyPreparedSpec : QuerySpec database Unit Nat .exactlyOne := {
  name := "legacy_manual"
  sql := "SELECT 11"
  contractHash := "legacy-contract"
  params := #[]
  columns := #[]
  encode := fun _ _ => pure { values := #[], formats := #[] }
  decode := fun _ _ _ => pure 11
  preparedDecode := some (fun _ _ _ _ => pure 22)
}

private def failed (result : Except Error Unit) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def okEq [BEq α] (result : Except Error α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def sameResult [BEq α] (left right : Except Error α) : Bool :=
  match left, right with
  | .ok left, .ok right => left == right
  | .error left, .error right =>
      left.kind == right.kind && left.toMessage == right.toMessage
  | _, _ => false

private def exactError (result : Except Error α) (kind : ErrorKind)
    (message : String) : Bool :=
  match result with
  | .error error => error.kind == kind && error.toMessage == message
  | .ok _ => false

private def isError (result : Except Error α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def isSchemaDrift (result : Except Error α) : Bool :=
  match result with
  | .error (.schemaDrift _) => true
  | .error _ | .ok _ => false

private def isQueryDrift (result : Except Error α) : Bool :=
  match result with
  | .error (.queryDrift _) => true
  | .error _ | .ok _ => false

private def preparationFailureTests : IO Unit := do
  let classified := preparationFailure (.transport "temporary socket failure")
  assert! match classified with
    | .postgres (.transport message) => message == "temporary socket failure"
    | _ => false
  assert! !isVerifiedDescriptorDrift classified
  assert! isVerifiedDescriptorDrift (.queryDrift "verified result descriptor mismatch")
  assert! !isVerifiedDescriptorDrift (.postgres .disconnected)

private def structuredErrorTests : IO Unit := do
  assert! Error.kind (.postgres .disconnected) == .postgres
  assert! Error.kind (.decode "bad payload") == .decode
  assert! Error.driftContext? (.schemaDrift "missing app.users") == some {
    kind := .schema
    message := "missing app.users"
  }
  assert! Error.driftContext? (.queryDrift "column changed") == some {
    kind := .query
    message := "column changed"
  }
  assert! Error.cardinalityContext? (.cardinality "one row" "3 rows") == some {
    expected := "one row"
    actual := "3 rows"
  }
  assert! match Error.postgres? (.postgres (.transport "temporary")) with
    | some (.transport message) => message == "temporary"
    | _ => false

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

private def preparedPlanTests (catalog : ResolvedCatalog database) : IO Unit := do
  let resolvedParams ← match resolvePreparedParams catalog #[param] with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  let textPlan ← match createPreparedQueryPlan catalog "query-key" "query-contract"
      #[param] resolvedParams #[column] #[] statement with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  assert! textPlan.params.size == 1
  assert! textPlan.params[0]!.oid == 23
  assert! textPlan.results[0]!.oid == 23
  assert! textPlan.columns[0]!.origin == some { tableOid := 90001, attnum := 1 }
  assert! textPlan.statementNameUtf8.val == statement.name.toUTF8
  -- The cached field remains optional at ordinary constructor call sites, so
  -- source using the former eight value arguments still elaborates.
  let legacyPositional : PreparedQueryPlan database :=
    PreparedQueryPlan.mk textPlan.cacheKey textPlan.contractHash textPlan.statement
      textPlan.params textPlan.results textPlan.resolve textPlan.columns
      textPlan.resultFormats
  assert! legacyPositional.statementNameUtf8.val == statement.name.toUTF8
  assert! (verifyPreparedQueryIdentity textPlan "query-key" "query-contract" 1 1 0).isOk
  assert! isError (verifyPreparedQueryIdentity textPlan
    "query-key" "different-parameter-contract" 1 1 0)
  assert! isError (verifyPreparedQueryIdentity textPlan
    "query-key" "different-format-contract" 1 1 1)
  assert! (verifyPreparedResultColumns textPlan #[idResult]).isOk
  assert! isError (verifyPreparedResultColumns textPlan
    #[{ idResult with typeOid := 25 }])
  assert! isError (verifyPreparedResultColumns textPlan
    #[{ idResult with tableOid := 90002 }])

  let nul := String.singleton (Char.ofNat 0)
  let unicodeStatement := { statement with name := "名" ++ nul ++ "🚀" }
  let unicodePlan ← match createPreparedQueryPlan catalog "unicode-key"
      "unicode-contract" #[param] resolvedParams #[column] #[] unicodeStatement with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  assert! unicodePlan.statementNameUtf8.val == unicodeStatement.name.toUTF8

  -- Bind format-vector validation is paid while constructing the plan.  The
  -- statement Describe remains text, while every portal description is still
  -- checked against the cached binary expectation before decoding.
  let binaryPlan ← match createPreparedQueryPlan catalog "binary-key" "binary-contract"
      #[param] resolvedParams #[column] #[1] statement with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  assert! binaryPlan.columns[0]!.format == 1
  assert! isError (verifyPreparedQueryIdentity binaryPlan
    "binary-key" "different-format-contract" 1 1 1)
  assert! (verifyPreparedResultColumns binaryPlan
    #[{ idResult with format := 1 }]).isOk
  assert! isError (verifyPreparedResultColumns binaryPlan #[idResult])
  let decoderEntered ← IO.mkRef false
  let verifyBeforeDecode (actual : Array Pg.Protocol.ColumnDesc) :
      IO (Except Error Unit) := do
    match verifyPreparedResultColumns binaryPlan actual with
    | .error error => pure (.error error)
    | .ok () =>
      decoderEntered.set true
      pure (.ok ())
  assert! isError (← verifyBeforeDecode #[idResult])
  assert! !(← decoderEntered.get)
  assert! (← verifyBeforeDecode #[{ idResult with format := 1 }]).isOk
  assert! ← decoderEntered.get
  assert! isError (createPreparedQueryPlan catalog "bad-key" "bad-contract"
    #[param] resolvedParams #[column] #[0, 1] statement)
  assert! isError (createPreparedQueryPlan catalog "bad-key" "bad-contract"
    #[param] resolvedParams #[column] #[2] statement)

  -- One cache has one first-use owner and publishes the same completed plan to
  -- followers.  A distinct cache (and therefore a distinct physical checked
  -- connection) has independent ownership for the identical full key.
  let cacheA : PreparedCache database ← Std.Mutex.new #[]
  let cacheB : PreparedCache database ← Std.Mutex.new #[]
  assert! match ← beginPrepareCache cacheA "query-key" with
    | .owner => true
    | _ => false
  assert! match ← beginPrepareCache cacheA "query-key" with
    | .wait _ => true
    | _ => false
  completePrepareCache cacheA "query-key" (.ok textPlan)
  assert! match ← beginPrepareCache cacheA "query-key" with
    | .ready plan => plan.statement.name == statement.name &&
        plan.statementNameUtf8.val == statement.name.toUTF8
    | _ => false
  assert! match ← beginPrepareCache cacheB "query-key" with
    | .owner => true
    | _ => false
  markPreparedCacheDrift cacheA "query-key" (.queryDrift "portal changed")
  assert! match ← beginPrepareCache cacheA "query-key" with
    | .failed (.queryDrift message) => message == "portal changed"
    | _ => false

  -- Release genuinely concurrent contenders through one barrier.  The mutex
  -- must publish exactly one preparation owner; every other task observes the
  -- same pending completion rather than becoming a second Parse owner.
  let concurrentCache : PreparedCache database ← Std.Mutex.new #[]
  let start : IO.Promise Unit ← IO.Promise.new
  let contenderCount := 16
  let mut contenders : Array (Std.Async.AsyncTask (PrepareDecision database)) := #[]
  for _ in [0:contenderCount] do
    contenders := contenders.push (← IO.asTask do
      let some () ← IO.wait start.result?
        | throw (IO.userError "concurrent cache barrier was dropped")
      beginPrepareCache concurrentCache "concurrent-key")
  discard <| start.resolve ()
  let mut owners := 0
  let mut waiters := 0
  for contender in contenders do
    match ← IO.wait contender with
    | .ok .owner => owners := owners + 1
    | .ok (.wait _) => waiters := waiters + 1
    | .ok _ => throw (IO.userError "concurrent first use observed a completed cache entry")
    | .error error => throw error
  assert! owners == 1
  assert! waiters == contenderCount - 1
  completePrepareCache concurrentCache "concurrent-key" (.ok textPlan)

  let retryCache : PreparedCache database ← Std.Mutex.new #[]
  assert! match ← beginPrepareCache retryCache "retry" with
    | .owner => true
    | _ => false
  completePrepareCache retryCache "retry"
    (.error (.postgres (.transport "temporary")))
  assert! match ← beginPrepareCache retryCache "retry" with
    | .owner => true
    | _ => false

  let driftCache : PreparedCache database ← Std.Mutex.new #[]
  assert! match ← beginPrepareCache driftCache "drift" with
    | .owner => true
    | _ => false
  completePrepareCache driftCache "drift" (.error (.queryDrift "changed"))
  assert! match ← beginPrepareCache driftCache "drift" with
    | .failed (.queryDrift message) => message == "changed"
    | _ => false

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
  let ownership : Array ExtensionTypeOwnership := #[{
    key := extensionKey
    extension := "citext"
  }]
  assert! (validateExtensionMetadata extensionDb
    #[("citext", "1.6"), ("plpgsql", "1.0")] ownership).isOk
  assert! isError (validateExtensionMetadata extensionDb
    #[("citext", "1.5")] ownership)
  assert! isError (validateExtensionMetadata extensionDb #[] ownership)
  assert! isError (validateExtensionMetadata {
    extensionDb with
    extensionCodecPackages := extensionDb.extensionCodecPackages.map fun package =>
      { package with version := "1.5" }
  } #[("citext", "1.6")] ownership)
  assert! isError (validateExtensionMetadata {
    extensionDb with types := database.types
  } #[("citext", "1.6")] ownership)
  assert! isError (validateExtensionMetadata extensionDb
    #[("citext", "1.6")] #[])
  assert! isError (validateExtensionMetadata extensionDb
    #[("citext", "1.6")]
    #[{ key := extensionKey, extension := "other" }])
  assert! isError (validateExtensionMetadata extensionDb
    #[("citext", "1.6")] (ownership ++ ownership))
  assert! extensionTypeOwnershipSql.contains
    "dep.classid = 'pg_catalog.pg_type'::pg_catalog.regclass"
  assert! extensionTypeOwnershipSql.contains
    "dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass"
  assert! extensionTypeOwnershipSql.contains "dep.objsubid = 0"
  assert! extensionTypeOwnershipSql.contains "dep.refobjsubid = 0"
  assert! extensionTypeOwnershipSql.contains "dep.deptype = 'e'"

private def relationalMetadataTests : IO Unit := do
  let int4Eq : Pgx.OperatorKey := {
    schema := "pg_catalog"
    name := "="
    leftType := int4Key
    rightType := int4Key
  }
  let textEq : Pgx.OperatorKey := {
    schema := "pg_catalog"
    name := "="
    leftType := textKey
    rightType := textKey
  }
  let idKey : Pgx.IndexKeyElementIR := {
    ordinal := 1
    column := some "id"
    opclass := some { schema := "pg_catalog", name := "int4_ops" }
    equalityOperator := some int4Eq
  }
  let emailKey : Pgx.IndexKeyElementIR := {
    ordinal := 2
    column := some "email"
    collation := some { schema := "pg_catalog", name := "default" }
    opclass := some { schema := "pg_catalog", name := "text_ops" }
    equalityOperator := some textEq
  }
  let uniqueIndex : Pgx.IndexIR := {
    relation := usersKey
    name := "users_id_email_key"
    unique := true
    primary := false
    valid := true
    accessMethod := some "btree"
    columns := #["id", "email"]
    keyElements := #[idKey, emailKey]
    includedColumns := #["email", "id"]
  }
  let performanceIndex : Pgx.IndexIR := {
    relation := usersKey
    name := "users_email_idx"
    unique := false
    primary := false
    valid := true
    columns := #["email"]
  }
  assert! (validateIndexMetadata #[uniqueIndex, performanceIndex]
    #[{ uniqueIndex with includedColumns := #["id", "email"] }]).isOk
  assert! isSchemaDrift (validateIndexMetadata #[uniqueIndex]
    #[{ uniqueIndex with valid := false }])
  assert! isError (validateIndexMetadata #[uniqueIndex]
    #[{ uniqueIndex with uniqueNullPolicy := .notDistinct }])
  assert! isError (validateIndexMetadata #[uniqueIndex]
    #[{ uniqueIndex with keyElements := #[emailKey, idKey] }])
  assert! isError (validateIndexMetadata #[uniqueIndex]
    #[{ uniqueIndex with keyElements := #[idKey,
      { emailKey with equalityOperator := some int4Eq }] }])
  assert! isError (validateIndexMetadata #[uniqueIndex, uniqueIndex] #[uniqueIndex, uniqueIndex])

  let organizationsKey : Pgx.RelationKey := { schema := "app", name := "organizations" }
  let fk : Pgx.ConstraintIR := {
    relation := usersKey
    name := "users_org_fkey"
    kind := .foreignKey
    columns := #["id", "email"]
    referencedRelation := some organizationsKey
    referencedColumns := #["id", "name"]
    deferrable := true
    initiallyDeferred := true
    supportingIndex := some { schema := "app", name := "organizations_id_name_key" }
    foreignKeyMatch := .full
    foreignKeyOnUpdate := .cascade
    foreignKeyOnDelete := .setNull
    foreignKeyDeleteSetColumns := #["email", "id"]
    referencedToReferencingOperators := #[int4Eq, textEq]
    referencedEqualityOperators := #[int4Eq, textEq]
    referencingEqualityOperators := #[int4Eq, textEq]
  }
  let check : Pgx.ConstraintIR := {
    relation := usersKey
    name := "users_id_check"
    kind := .check
    columns := #["id"]
    expression := some "CHECK ((id > 0))"
    localExpression := some (.constant (some true))
    noInherit := true
  }
  assert! (validateConstraintMetadata #[fk, check] #[
    { check with localExpression := none },
    { fk with foreignKeyDeleteSetColumns := #["id", "email"] }
  ]).isOk
  assert! isSchemaDrift (validateConstraintMetadata #[fk]
    #[{ fk with validated := false }])
  assert! isError (validateConstraintMetadata #[fk]
    #[{ fk with initiallyDeferred := false }])
  assert! isError (validateConstraintMetadata #[fk]
    #[{ fk with referencedColumns := fk.referencedColumns.reverse }])
  assert! isError (validateConstraintMetadata #[fk]
    #[{ fk with referencedToReferencingOperators :=
      fk.referencedToReferencingOperators.reverse }])
  assert! isError (validateConstraintMetadata #[fk, fk] #[fk, fk])

  let nativeNotNull : Pgx.ConstraintIR := {
    relation := usersKey
    name := "users_email_not_null"
    kind := .notNull
    columns := #["email"]
  }
  assert! (validateNotNullReadSafety 18 #[nativeNotNull]).isOk
  assert! isSchemaDrift (validateNotNullReadSafety 18
    #[{ nativeNotNull with validated := false }])
  assert! isError (validateNotNullReadSafety 18
    #[{ nativeNotNull with enforced := false }])
  -- PostgreSQL 17 has no native relation NOT NULL catalog row; its canonical
  -- constraints are synthesized only after `attnotnull` is trusted.
  assert! (validateNotNullReadSafety 17
    #[{ nativeNotNull with validated := false }]).isOk

  let pg17 := relationalConstraintCatalogSql 17
  let pg18 := relationalConstraintCatalogSql 18
  assert! !pg17.contains "con.conenforced"
  assert! !pg17.contains "con.conperiod"
  assert! !pg17.contains "'n'"
  assert! pg18.contains "con.conenforced"
  assert! pg18.contains "con.conperiod"
  assert! pg18.contains "'n'"
  assert! (relationalConstraintColumnSql 17).contains "WITH ORDINALITY"
  assert! relationalConstraintDeleteSetColumnSql.contains "confdelsetcols"
  assert! relationalConstraintOperatorSql.contains "conpfeqop"
  assert! relationalConstraintOperatorSql.contains "conppeqop"
  assert! relationalConstraintOperatorSql.contains "conffeqop"
  assert! relationalConstraintOperatorSql.contains "conexclop"
  assert! relationalIndexCatalogSql.contains "indnullsnotdistinct"
  assert! relationalIndexElementSql.contains "indnkeyatts"
  assert! relationalIndexElementSql.contains "pg_catalog.pg_amop"
  assert! relationalIndexElementSql.contains "AS coll_item("
  assert! !relationalIndexElementSql.contains "AS collation("
  assert! !(relationalConstraintColumnSql 17).contains "item.ordinality::text"
  assert! !relationalConstraintOperatorSql.contains "item.ordinality::text"

def main : IO UInt32 := do
  preparationFailureTests
  structuredErrorTests
  resolvedCodecTests
  semanticMetadataTests
  relationalMetadataTests
  let catalog ← match catalogResult with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  preparedPlanTests catalog
  assert! (verifyStatement catalog #[param] #[column] statement).isOk
  assert! (verifyResultColumns catalog #[column] #[idResult]).isOk
  assert! (verifyResultColumns catalog #[column] #[idResult] #[0]).isOk
  assert! (verifyResultColumns catalog #[column]
    #[{ idResult with format := 1 }] #[1]).isOk
  assert! (verifyResultColumns catalog #[column, column]
    #[{ idResult with format := 1 }, { idResult with format := 1 }] #[1]).isOk
  assert! failed (verifyResultColumns catalog #[column] #[idResult] #[1])
  assert! failed (verifyResultColumns catalog #[column] #[idResult] #[0, 1])
  assert! failed (verifyResultColumns catalog #[column, column]
    #[idResult, idResult] #[0, 0, 0])
  assert! failed (verifyResultColumns catalog #[column] #[idResult] #[2])
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
  let escapedBytea := "borrowed descriptor payload".toUTF8
  assert! okEq (decodeOwnedPlannedBytea (some escapedBytea)) escapedBytea
  assert! legacyPreparedSpec.preparedDecode.isSome
  assert! legacyPreparedSpec.preparedSpanDecode.isNone
  assert! legacyPreparedSpec.preparedSpanDecoderBundle.isNone
  let binarySpanRow := Pg.Protocol.DataRowSpans.ofCells
    #[some "prefix".toUTF8,
      some (Pg.Protocol.putUInt32 ByteArray.empty (UInt32.ofNat 42)), none]
  assert! okEq
    (decodePlannedBuiltinSpan (α := Int32) Pg.Oid.int4 1 binarySpanRow 1) 42
  if h : 1 < binarySpanRow.size then
    assert! sameResult
      (decodePlannedBuiltinSpan (α := Int32) Pg.Oid.int4 1 binarySpanRow 1)
      (decodePlannedBuiltinSpanAt (α := Int32) Pg.Oid.int4 1 binarySpanRow 1 h)
    assert! sameResult
      (decodePlannedBuiltinSpanAt (α := Int32) Pg.Oid.int4 1 binarySpanRow 1 h)
      (decodePlannedBuiltinBinarySpanAt (α := Int32) Pg.Oid.int4 binarySpanRow 1 h)
  else
    throw (IO.userError "binary span fixture lost its decoded cell")
  assert! okEq
    (decodePlannedBuiltinSpan (α := Option Int32) Pg.Oid.int4 1 binarySpanRow 2) none
  if h : 2 < binarySpanRow.size then
    assert! sameResult
      (decodePlannedBuiltinSpan (α := Option Int32) Pg.Oid.int4 1 binarySpanRow 2)
      (decodePlannedBuiltinSpanAt (α := Option Int32) Pg.Oid.int4 1 binarySpanRow 2 h)
    assert! sameResult
      (decodePlannedBuiltinSpanAt (α := Option Int32) Pg.Oid.int4 1 binarySpanRow 2 h)
      (decodePlannedBuiltinBinarySpanAt (α := Option Int32)
        Pg.Oid.int4 binarySpanRow 2 h)
  else
    throw (IO.userError "binary span fixture lost its NULL cell")
  assert! isError
    (decodePlannedBuiltinSpan (α := Int32) Pg.Oid.int4 1 binarySpanRow 3)
  let probePrefix := "nonzero-prefix".toUTF8
  let probePayload := Pg.putInt64BE 42
  let probeSuffix := "distinct-suffix".toUTF8
  let probeRow := Pg.Protocol.DataRowSpans.ofCells
    #[some probePrefix, some probePayload, some probeSuffix]
  let expectedProbe : SpanProbe := {
    ownerSize := probePrefix.size + probePayload.size + probeSuffix.size
    offset := probePrefix.size
    length := probePayload.size
  }
  assert! okEq
    (decodePlannedBuiltinSpan (α := SpanProbe) Pg.Oid.int8 1 probeRow 1)
    expectedProbe
  if h : 1 < probeRow.size then
    assert! sameResult
      (decodePlannedBuiltinSpan (α := SpanProbe) Pg.Oid.int8 1 probeRow 1)
      (decodePlannedBuiltinSpanAt (α := SpanProbe) Pg.Oid.int8 1 probeRow 1 h)
    assert! sameResult
      (decodePlannedBuiltinSpanAt (α := SpanProbe) Pg.Oid.int8 1 probeRow 1 h)
      (decodePlannedBuiltinBinarySpanAt (α := SpanProbe) Pg.Oid.int8 probeRow 1 h)
  else
    throw (IO.userError "span-probe fixture lost its decoded cell")
  let malformedBinaryRow := Pg.Protocol.DataRowSpans.ofCells
    #[some (ByteArray.mk #[0xff])]
  if h : 0 < malformedBinaryRow.size then
    let reference :=
      decodePlannedBuiltinSpan (α := Int32) Pg.Oid.int4 1 malformedBinaryRow 0
    let candidate :=
      decodePlannedBuiltinSpanAt (α := Int32) Pg.Oid.int4 1 malformedBinaryRow 0 h
    let fixedCandidate :=
      decodePlannedBuiltinBinarySpanAt (α := Int32) Pg.Oid.int4 malformedBinaryRow 0 h
    assert! sameResult reference candidate
    assert! sameResult candidate fixedCandidate
    assert! exactError candidate .decode
      "row decoding failed: unexpected integer width 1"
    assert! exactError fixedCandidate .decode
      "row decoding failed: unexpected integer width 1"
  else
    throw (IO.userError "malformed-binary fixture lost its decoded cell")
  let invalidUtf8Row := Pg.Protocol.DataRowSpans.ofCells
    #[some (ByteArray.mk #[0xff])]
  if h : 0 < invalidUtf8Row.size then
    let reference :=
      decodePlannedBuiltinSpan (α := String) Pg.Oid.text 0 invalidUtf8Row 0
    let candidate :=
      decodePlannedBuiltinSpanAt (α := String) Pg.Oid.text 0 invalidUtf8Row 0 h
    let fixedCandidate :=
      decodePlannedBuiltinTextSpanAt (α := String) Pg.Oid.text invalidUtf8Row 0 h
    assert! sameResult reference candidate
    assert! sameResult candidate fixedCandidate
    assert! exactError candidate .decode
      "row decoding failed: text value is not valid UTF-8"
    assert! exactError fixedCandidate .decode
      "row decoding failed: text value is not valid UTF-8"
  else
    throw (IO.userError "invalid-UTF8 fixture lost its decoded cell")
  let textSpanRow := Pg.Protocol.DataRowSpans.ofCells
    #[some "ignored".toUTF8, some "42".toUTF8]
  if h : 1 < textSpanRow.size then
    assert! sameResult
      (decodePlannedBuiltinSpanAt (α := Int32) Pg.Oid.int4 0 textSpanRow 1 h)
      (decodePlannedBuiltinTextSpanAt (α := Int32) Pg.Oid.int4 textSpanRow 1 h)
  else
    throw (IO.userError "text span fixture lost its decoded cell")
  assert! okEq
    (decodePlannedSpan int4Codec resolveTestType
      { expected := int4Desc, oid := Pg.Oid.int4 } 0 textSpanRow 1) 42
  assert! isError
    (decodePlannedSpan int4Codec resolveTestType
      { expected := int4Desc, oid := Pg.Oid.int4 } 0 textSpanRow 2)
  let selectedCell := "only-this-cell".toUTF8
  let echoRow := Pg.Protocol.DataRowSpans.ofCells
    #[some "left-sibling".toUTF8, some selectedCell, some "right-sibling".toUTF8]
  assert! okEq
    (decodePlannedSpan echoCodec resolveTestType
      { expected := int4Desc, oid := Pg.Oid.int4 } 1 echoRow 1) selectedCell
  assert! isQueryDrift
    (decodePlannedSpan echoCodec resolveTestType
      { expected := int4Desc, oid := Pg.Oid.int4 } 1 echoRow 3)
  let encoded ← match encodeBuiltin catalog int4 (42 : Int32) with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  assert! encoded.format == 0
  assert! encoded.value == some "42".toUTF8
  assert! toString (Error.constraintViolation
    (.checkFailed "users_display_name_not_blank")) ==
      "local constraint violation: PostgreSQL check users_display_name_not_blank evaluated to false"
  return 0
