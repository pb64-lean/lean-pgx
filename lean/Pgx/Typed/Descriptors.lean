import Pgx.IR
import Pg

/-!
# Checked PostgreSQL descriptors

These declarations form the trust boundary between generated symbolic
contracts and installation-local PostgreSQL descriptors.  Decoding is only
performed after the functions at the end of this module have accepted the
wire descriptors.
-/

namespace Pgx.Typed

inductive Error where
  | postgres (error : Pg.Error)
  | schemaDrift (message : String)
  | queryDrift (message : String)
  | unsupportedType (key : Pgx.TypeKey)
  | encode (message : String)
  | decode (message : String)
  | cardinality (expected actual : String)
  deriving Repr, Inhabited

namespace Error

def toMessage : Error → String
  | .postgres error => toString error
  | .schemaDrift message => s!"schema drift: {message}"
  | .queryDrift message => s!"query drift: {message}"
  | .unsupportedType key => s!"unsupported PostgreSQL type: {key}"
  | .encode message => s!"parameter encoding failed: {message}"
  | .decode message => s!"row decoding failed: {message}"
  | .cardinality expected actual =>
      s!"cardinality mismatch: expected {expected}, got {actual}"

end Error

instance : ToString Error := ⟨Error.toMessage⟩

structure StaticTypeDesc where
  key : Pgx.TypeKey
  base : Option Pgx.TypeRef := none
  enumLabels : Array String := #[]
  notNull : Bool := false
  deriving Repr, BEq, Inhabited

structure StaticColumnDesc where
  name : String
  ordinal : Nat
  ty : Pgx.TypeRef
  nullable : Bool
  deriving Repr, BEq, Inhabited

structure StaticRelationDesc where
  key : Pgx.RelationKey
  kind : Pgx.RelationKind
  columns : Array StaticColumnDesc
  deriving Repr, BEq, Inhabited

structure DatabaseDesc where
  canonicalMajor : Nat
  serverMajors : Array Nat
  session : Pgx.SessionContract
  types : Array StaticTypeDesc
  relations : Array StaticRelationDesc
  schemaHash : String
  contractHash : String
  deriving Repr, BEq, Inhabited

structure ResolvedType where
  expected : StaticTypeDesc
  oid : UInt32
  arrayOid : Option UInt32 := none
  deriving Repr, BEq, Inhabited

structure ResolvedColumn where
  expected : StaticColumnDesc
  attnum : UInt16
  deriving Repr, BEq, Inhabited

structure ResolvedRelation where
  expected : StaticRelationDesc
  oid : UInt32
  columns : Array ResolvedColumn
  deriving Repr, BEq, Inhabited

/-- Symbolic-to-physical resolution accepted against a particular generated
database descriptor.  Its constructor is private; `create` verifies exact
coverage of the static descriptors. -/
structure ResolvedCatalog (db : DatabaseDesc) where
  private mk ::
  private resolvedTypes : Array ResolvedType
  private resolvedRelations : Array ResolvedRelation

namespace ResolvedCatalog

private def uniqueTypeKeys (values : Array ResolvedType) : Bool := Id.run do
  for i in [0:values.size] do
    for j in [i + 1:values.size] do
      if values[i]!.expected.key == values[j]!.expected.key then return false
  return true

private def uniqueRelationKeys (values : Array ResolvedRelation) : Bool := Id.run do
  for i in [0:values.size] do
    for j in [i + 1:values.size] do
      if values[i]!.expected.key == values[j]!.expected.key then return false
  return true

/-- Validate complete, duplicate-free symbolic coverage before sealing a
resolved catalog.  Physical OID values are deliberately not prescribed. -/
def create (db : DatabaseDesc)
    (types : Array ResolvedType) (relations : Array ResolvedRelation) :
    Except Error (ResolvedCatalog db) := do
  unless types.size == db.types.size do
    throw (.schemaDrift s!"resolved {types.size} types; expected {db.types.size}")
  unless relations.size == db.relations.size do
    throw (.schemaDrift
      s!"resolved {relations.size} relations; expected {db.relations.size}")
  unless uniqueTypeKeys types do
    throw (.schemaDrift "resolved catalog contains duplicate type keys")
  unless uniqueRelationKeys relations do
    throw (.schemaDrift "resolved catalog contains duplicate relation keys")
  for expected in db.types do
    let some actual := types.find? (fun value => value.expected.key == expected.key)
      | throw (.schemaDrift s!"type {expected.key} was not resolved")
    unless actual.expected == expected do
      throw (.schemaDrift s!"type metadata changed for {expected.key}")
  for expected in db.relations do
    let some actual := relations.find? (fun value => value.expected.key == expected.key)
      | throw (.schemaDrift s!"relation {expected.key} was not resolved")
    unless actual.expected == expected do
      throw (.schemaDrift s!"relation metadata changed for {expected.key}")
    unless actual.columns.size == expected.columns.size do
      throw (.schemaDrift s!"relation column resolution changed for {expected.key}")
    for column in expected.columns do
      let some resolved := actual.columns.find? (fun value =>
          value.expected.name == column.name)
        | throw (.schemaDrift s!"column {expected.key}.{column.name} was not resolved")
      unless resolved.expected == column do
        throw (.schemaDrift s!"column metadata changed for {expected.key}.{column.name}")
  pure (.mk types relations)

def types (catalog : ResolvedCatalog db) : Array ResolvedType := catalog.resolvedTypes

def relations (catalog : ResolvedCatalog db) : Array ResolvedRelation :=
  catalog.resolvedRelations

def resolveType? (catalog : ResolvedCatalog db) (key : Pgx.TypeKey) : Option ResolvedType :=
  catalog.resolvedTypes.find? (fun value => value.expected.key == key)

def resolveType (catalog : ResolvedCatalog db) (key : Pgx.TypeKey) :
    Except Error ResolvedType :=
  match catalog.resolveType? key with
  | some value => .ok value
  | none => .error (.unsupportedType key)

def resolveRelation? (catalog : ResolvedCatalog db) (key : Pgx.RelationKey) :
    Option ResolvedRelation :=
  catalog.resolvedRelations.find? (fun value => value.expected.key == key)

def origin? (catalog : ResolvedCatalog db) (tableOid : UInt32) (attnum : UInt16) :
    Option Pgx.ColumnKey := do
  let relation ← catalog.resolvedRelations.find? (fun value => value.oid == tableOid)
  let column ← relation.columns.find? (fun value => value.attnum == attnum)
  pure { relation := relation.expected.key, name := column.expected.name }

end ResolvedCatalog

structure ParamSpec where
  name : String
  ty : Pgx.TypeRef
  nullable : Bool
  deriving Repr, BEq, Inhabited

structure ColumnSpec where
  name : String
  ty : Pgx.TypeRef
  nullable : Bool
  origin : Option Pgx.ColumnKey := none
  deriving Repr, BEq, Inhabited

structure EncodedValue where
  format : UInt16
  value : Option ByteArray
  deriving Repr, BEq, Inhabited

structure EncodedParams where
  values : Array (Option ByteArray)
  formats : Array UInt16
  deriving Repr, BEq, Inhabited

structure CommandResult where
  tag : String
  deriving Repr, BEq, Inhabited

def QueryResult (cardinality : Pgx.Cardinality) (row : Type) : Type :=
  match cardinality with
  | .execute => CommandResult
  | .exactlyOne => row
  | .zeroOrOne => Option row
  | .many => Array row

structure ResolvedCodec (α : Type) where
  expected : StaticTypeDesc
  encode : ResolvedType → α → Except Error EncodedValue
  decode : ResolvedType → UInt16 → Option ByteArray → Except Error α

namespace ResolvedCodec

def option (codec : ResolvedCodec α) : ResolvedCodec (Option α) where
  expected := codec.expected
  encode resolved
    | none => pure { format := 0, value := none }
    | some value => codec.encode resolved value
  decode resolved format
    | none => pure none
    | some bytes => some <$> codec.decode resolved format (some bytes)

end ResolvedCodec

def encodeBuiltin [Pg.PgEncode α] (catalog : ResolvedCatalog db)
    (ty : Pgx.TypeRef) (value : α) : Except Error EncodedValue := do
  let _ ← catalog.resolveType ty.key
  pure {
    format := Pg.PgEncode.format α
    value := Pg.PgEncode.encode value
  }

def decodeBuiltin [Pg.PgDecode α] (catalog : ResolvedCatalog db)
    (ty : Pgx.TypeRef) (format : UInt16) (value : Option ByteArray) : Except Error α := do
  let resolved ← catalog.resolveType ty.key
  match Pg.decodeValue (α := α) resolved.oid format value with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

def encodeResolved (codec : ResolvedCodec α) (catalog : ResolvedCatalog db)
    (ty : Pgx.TypeRef) (value : α) : Except Error EncodedValue := do
  let resolved ← catalog.resolveType ty.key
  unless resolved.expected == codec.expected do
    throw (.schemaDrift s!"codec does not describe {ty.key}")
  codec.encode resolved value

def decodeResolved (codec : ResolvedCodec α) (catalog : ResolvedCatalog db)
    (ty : Pgx.TypeRef) (format : UInt16) (value : Option ByteArray) : Except Error α := do
  let resolved ← catalog.resolveType ty.key
  unless resolved.expected == codec.expected do
    throw (.schemaDrift s!"codec does not describe {ty.key}")
  codec.decode resolved format value

structure QuerySpec (db : DatabaseDesc) (Params Row : Type)
    (cardinality : Pgx.Cardinality) where
  name : String
  sql : String
  contractHash : String
  params : Array ParamSpec
  columns : Array ColumnSpec
  encode : ResolvedCatalog db → Params → Except Error EncodedParams
  decode : ResolvedCatalog db → Array Pg.Protocol.ColumnDesc →
    Array (Option ByteArray) → Except Error Row

private def expectedOid (catalog : ResolvedCatalog db) (ref : Pgx.TypeRef) :
    Except Error UInt32 := do
  pure (← catalog.resolveType ref.key).oid

private def verifyColumns (catalog : ResolvedCatalog db)
    (expected : Array ColumnSpec) (actual : Array Pg.Protocol.ColumnDesc) :
    Except Error Unit := do
  unless actual.size == expected.size do
    throw (.queryDrift
      s!"result column count changed from {expected.size} to {actual.size}")
  for i in [0:expected.size] do
    let want := expected[i]!
    let got := actual[i]!
    unless got.name == want.name do
      throw (.queryDrift
        s!"result column {i + 1} changed name from {want.name} to {got.name}")
    let oid ← expectedOid catalog want.ty
    unless got.typeOid == oid do
      throw (.queryDrift
        s!"result column {want.name} changed PostgreSQL type")
    -- PostgreSQL encodes the absence of a type modifier as `-1` on the
    -- wire.  Compare that sentinel as well: changing an unbounded value to a
    -- bounded one must be query drift, not an unchecked descriptor change.
    let expectedTypeMod := want.ty.typmod.getD (-1)
    unless got.typeMod == expectedTypeMod do
      throw (.queryDrift
        s!"result column {want.name} changed type modifier")
    match want.origin with
    | some origin =>
      unless catalog.origin? got.tableOid got.attnum == some origin do
        throw (.queryDrift
          s!"result column {want.name} changed symbolic origin")
    | none => pure ()

def verifyResultColumns (catalog : ResolvedCatalog db)
    (expected : Array ColumnSpec) (actual : Array Pg.Protocol.ColumnDesc) :
    Except Error Unit :=
  verifyColumns catalog expected actual

def verifyStatement (catalog : ResolvedCatalog db)
    (params : Array ParamSpec) (columns : Array ColumnSpec) (statement : Pg.Statement) :
    Except Error Unit := do
  unless statement.paramTypes.size == params.size do
    throw (.queryDrift
      s!"parameter count changed from {params.size} to {statement.paramTypes.size}")
  for i in [0:params.size] do
    let oid ← expectedOid catalog params[i]!.ty
    unless statement.paramTypes[i]! == oid do
      throw (.queryDrift s!"parameter {i + 1} changed PostgreSQL type")
  verifyColumns catalog columns statement.columns

end Pgx.Typed
