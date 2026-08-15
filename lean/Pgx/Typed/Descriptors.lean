module

public import Pgx.IR
public import Pgx.Constraint.Semantics
public import Pg

public section

/-!
# Checked PostgreSQL descriptors

These declarations form the trust boundary between generated symbolic
contracts and installation-local PostgreSQL descriptors.  Decoding is only
performed after the functions at the end of this module have accepted the
wire descriptors.
-/

namespace Pgx.Typed

/-- Stable, payload-independent classification for runtime failures. -/
inductive ErrorKind where
  | postgres
  | schemaDrift
  | queryDrift
  | unsupportedType
  | constraintViolation
  | encode
  | decode
  | cardinality
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Which checked contract produced a drift diagnostic. -/
inductive DriftKind where
  | schema
  | query
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Structured view of a schema- or query-drift diagnostic. -/
structure DriftContext where
  kind : DriftKind
  message : String
  deriving Repr, BEq, Inhabited

/-- Structured view of a generated cardinality-contract failure. -/
structure CardinalityContext where
  expected : String
  actual : String
  deriving Repr, BEq, Inhabited

inductive Error where
  | postgres (error : Pg.Error)
  | schemaDrift (message : String)
  | queryDrift (message : String)
  | unsupportedType (key : Pgx.TypeKey)
  | constraintViolation (violation : Pgx.ConstraintViolation)
  | encode (message : String)
  | decode (message : String)
  | cardinality (expected actual : String)
  deriving Repr, Inhabited

namespace Error

/-- Classify an error without parsing its rendered message. -/
def kind : Error → ErrorKind
  | .postgres _ => .postgres
  | .schemaDrift _ => .schemaDrift
  | .queryDrift _ => .queryDrift
  | .unsupportedType _ => .unsupportedType
  | .constraintViolation _ => .constraintViolation
  | .encode _ => .encode
  | .decode _ => .decode
  | .cardinality _ _ => .cardinality

/-- Recover the original pg-lean error when this is a PostgreSQL failure. -/
def postgres? : Error → Option Pg.Error
  | .postgres error => some error
  | _ => none

/-- Recover structured drift scope and diagnostic text. -/
def driftContext? : Error → Option DriftContext
  | .schemaDrift message => some { kind := .schema, message }
  | .queryDrift message => some { kind := .query, message }
  | _ => none

/-- Recover structured cardinality details without parsing `toString`. -/
def cardinalityContext? : Error → Option CardinalityContext
  | .cardinality expected actual => some { expected, actual }
  | _ => none

def toMessage : Error → String
  | .postgres error => toString error
  | .schemaDrift message => s!"schema drift: {message}"
  | .queryDrift message => s!"query drift: {message}"
  | .unsupportedType key => s!"unsupported PostgreSQL type: {key}"
  | .constraintViolation violation => s!"local constraint violation: {violation}"
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
  arrayElement : Option Pgx.TypeRef := none
  arrayDelimiter : Option String := none
  compositeFields : Array Pgx.CompositeFieldIR := #[]
  rangeSubtype : Option Pgx.TypeRef := none
  rangeMultirange : Option Pgx.TypeKey := none
  rangeCollation : Option Pgx.CollationKey := none
  rangeSubtypeOpclass : Option Pgx.QualifiedName := none
  rangeCanonical : Option Pgx.RoutineKey := none
  rangeSubtypeDiff : Option Pgx.RoutineKey := none
  multirangeRange : Option Pgx.TypeKey := none
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
  /-- Symbolic relational constraints checked against the live catalog before
  a connection becomes usable by generated code. -/
  constraints : Array Pgx.ConstraintIR := #[]
  /-- Index metadata needed by relational constraints.  Attachment compares
  semantic (unique, primary-key, and exclusion) indexes; ordinary
  performance-only indexes remain descriptive IR. -/
  indexes : Array Pgx.IndexIR := #[]
  views : Array Pgx.ViewIR := #[]
  routines : Array Pgx.RoutineIR := #[]
  requiredExtensions : Array (String × String) := #[]
  extensionCodecPackages : Array Pgx.ExtensionCodecPackageIR := #[]
  /-- Legacy name retained for source compatibility. Generated descriptors set
  this to `contractHash`; new code should use `contractHash`. -/
  schemaHash : String
  /-- Fingerprint of the generated schema, query, session, and codec contract. -/
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

/-- Full prepared-query cache identity. Generated query modules evaluate this
at generation time and embed the resulting hexadecimal digest as a string
literal, keeping SHA-256 and its input construction off the execution path. -/
def queryCacheKey (databaseContractHash queryContractHash sql : String) : String :=
  Pg.Crypto.toHexLower <| Pg.Crypto.sha256
    (databaseContractHash ++ "\n" ++ queryContractHash ++ "\n" ++ sql).toUTF8

structure CommandResult where
  tag : String
  deriving Repr, BEq, Inhabited

def QueryResult (cardinality : Pgx.Cardinality) (row : Type) : Type :=
  match cardinality with
  | .execute => CommandResult
  | .exactlyOne => row
  | .zeroOrOne => Option row
  | .many => Array row

abbrev TypeResolver := Pgx.TypeKey → Except Error ResolvedType

/-- A codec whose symbolic descriptor has been attached to a live catalog.
The resolver is explicit because generated container and domain codecs must
resolve their component types without retaining a connection-specific OID. -/
structure ResolvedCodec (α : Type) where
  expected : StaticTypeDesc
  encode : TypeResolver → ResolvedType → α → Except Error EncodedValue
  decode : TypeResolver → ResolvedType → UInt16 → Option ByteArray → Except Error α

namespace ResolvedCodec

def option (codec : ResolvedCodec α) : ResolvedCodec (Option α) where
  expected := codec.expected
  encode resolve resolved
    | none => pure { format := 0, value := none }
    | some value => codec.encode resolve resolved value
  decode resolve resolved format
    | none => pure none
    | some bytes => some <$> codec.decode resolve resolved format (some bytes)

private def checkedResolved (codec : ResolvedCodec α) (resolve : TypeResolver)
    (ty : Pgx.TypeRef) : Except Error ResolvedType := do
  let resolved ← resolve ty.key
  unless resolved.expected == codec.expected do
    throw (.schemaDrift s!"codec does not describe {ty.key}")
  pure resolved

/-- Render a non-NULL value through a resolved codec for embedding in a
container's text representation.  A binary-only extension codec is rejected
instead of having its bytes reinterpreted as text. -/
def encodeText (codec : ResolvedCodec α) (resolve : TypeResolver)
    (ty : Pgx.TypeRef) (value : α) : Except Error String := do
  let resolved ← checkedResolved codec resolve ty
  let encoded ← codec.encode resolve resolved value
  unless encoded.format == 0 do
    throw (.encode s!"codec for {ty.key} cannot encode container text")
  let some bytes := encoded.value
    | throw (.encode s!"codec for non-NULL {ty.key} encoded NULL")
  let some text := String.fromUTF8? bytes
    | throw (.encode s!"codec for {ty.key} produced non-UTF-8 text")
  pure text

/-- Decode a non-NULL text component through a resolved codec. -/
def decodeText (codec : ResolvedCodec α) (resolve : TypeResolver)
    (ty : Pgx.TypeRef) (value : String) : Except Error α := do
  let resolved ← checkedResolved codec resolve ty
  codec.decode resolve resolved 0 (some value.toUTF8)

/-- Decode a non-NULL binary component through a resolved codec after
checking the OID supplied by its enclosing binary value. -/
def decodeBinary (codec : ResolvedCodec α) (resolve : TypeResolver)
    (ty : Pgx.TypeRef) (actualOid : UInt32) (value : ByteArray) : Except Error α := do
  let resolved ← checkedResolved codec resolve ty
  unless actualOid == resolved.oid do
    throw (.decode s!"component OID mismatch for {ty.key}: expected \
      {resolved.oid}, got {actualOid}")
  codec.decode resolve resolved 1 (some value)

end ResolvedCodec

/-- Convert a typed runtime error into the callback error expected by the
pure container parsers. -/
def asStringError : Except Error α → Except String α
  | .ok value => .ok value
  | .error error => .error error.toMessage

def fromEncodeStringError : Except String α → Except Error α
  | .ok value => .ok value
  | .error message => .error (.encode message)

def fromDecodeStringError : Except String α → Except Error α
  | .ok value => .ok value
  | .error message => .error (.decode message)

/-- Render a built-in non-NULL value as text for a generated container codec. -/
def encodeBuiltinText [Pg.PgEncode α] (value : α) : Except Error String := do
  unless Pg.PgEncode.format α == 0 do
    throw (.encode "built-in codec has no text encoder")
  let some bytes := Pg.PgEncode.encode value
    | throw (.encode "built-in codec encoded a non-NULL value as NULL")
  let some text := String.fromUTF8? bytes
    | throw (.encode "built-in text codec produced non-UTF-8 data")
  pure text

/-- Decode a built-in text component using the component's resolved OID. -/
def decodeBuiltinText [Pg.PgDecode α] (resolved : ResolvedType)
    (value : String) : Except Error α :=
  match Pg.decodeValue (α := α) resolved.oid 0 (some value.toUTF8) with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

/-- Decode a built-in binary component after validating its enclosing OID. -/
def decodeBuiltinBinary [Pg.PgDecode α] (resolved : ResolvedType)
    (actualOid : UInt32) (value : ByteArray) : Except Error α := do
  unless actualOid == resolved.oid do
    throw (.decode s!"component OID mismatch for {resolved.expected.key}: expected \
      {resolved.oid}, got {actualOid}")
  match Pg.decodeValue (α := α) resolved.oid 1 (some value) with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

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
  codec.encode (fun key => catalog.resolveType key) resolved value

def decodeResolved (codec : ResolvedCodec α) (catalog : ResolvedCatalog db)
    (ty : Pgx.TypeRef) (format : UInt16) (value : Option ByteArray) : Except Error α := do
  let resolved ← catalog.resolveType ty.key
  unless resolved.expected == codec.expected do
    throw (.schemaDrift s!"codec does not describe {ty.key}")
  codec.decode (fun key => catalog.resolveType key) resolved format value

structure QuerySpec (db : DatabaseDesc) (Params Row : Type)
    (cardinality : Pgx.Cardinality) where
  name : String
  sql : String
  contractHash : String
  /-- Generation-time `queryCacheKey`. The empty default preserves manually
  authored source compatibility; generated specs always embed a nonempty key,
  while legacy/manual specs derive it on demand. -/
  cacheKey : String := ""
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
