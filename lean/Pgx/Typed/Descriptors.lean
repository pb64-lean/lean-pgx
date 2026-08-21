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
    (ty : Pgx.TypeRef) (format : UInt16) (value : @& Option ByteArray) : Except Error α := do
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

/-- Encode through a generated built-in codec on the planned path.  Built-in
encoders do not need an installation-local OID, so they avoid even the cached
descriptor array access after plan identity and arity have been checked. -/
def encodePlannedBuiltin [Pg.PgEncode α] (value : α) : Except Error EncodedValue :=
  pure {
    format := Pg.PgEncode.format α
    value := Pg.PgEncode.encode value
  }

/-- Obtain a built-in parameter's static wire format while letting generated
code construct its value array directly.  The borrowed witness keeps this
helper allocation-free even for reference-valued parameter types. -/
@[inline] def plannedBuiltinFormat [Pg.PgEncode α] (_ : @& α) : UInt16 :=
  Pg.PgEncode.format α

/-- Decode a built-in value using the portal OID that the numeric prepared plan
has already validated. -/
def decodePlannedBuiltin [Pg.PgDecode α] (typeOid : UInt32)
    (format : UInt16) (value : @& Option ByteArray) : Except Error α :=
  match Pg.decodeValue (α := α) typeOid format value with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

/-- Decode a generated custom-codec result from one materialized cell in an
otherwise row-owned span representation. -/
def decodePlannedSpan (codec : ResolvedCodec α) (resolve : TypeResolver)
    (resolved : ResolvedType) (format : UInt16)
    (row : @& Pg.Protocol.DataRowSpans) (index : Nat) : Except Error α := do
  let some value := row.cell? index
    | throw (.queryDrift s!"generated decoder is missing result column {index}")
  codec.decode resolve resolved format value

/-- Decode a built-in prepared result directly from its row-owned span. -/
def decodePlannedBuiltinSpan [Pg.PgDecode α] [Pg.PgDecodeSpan α] (typeOid : UInt32)
    (format : UInt16) (row : @& Pg.Protocol.DataRowSpans) (index : Nat) : Except Error α :=
  match Pg.decodeDataRowValue (α := α) typeOid format row index with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

/-- Decode a built-in prepared result after the generated row decoder has
proved that the result column is present.  This preserves the established
`Error.decode` mapping while avoiding a second, impossible span-index check. -/
def decodePlannedBuiltinSpanAt [Pg.PgDecode α] [Pg.PgDecodeSpan α]
    (typeOid : UInt32) (format : UInt16) (row : @& Pg.Protocol.DataRowSpans)
    (index : Nat) (h : index < row.size) : Except Error α :=
  match Pg.decodeDataRowValueAt (α := α) typeOid format row index h with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

/-- Decode a built-in binary-format result after generated batch dispatch has
proved both that the column is present and that the prepared format is binary.
The fixed-format pg-lean entry point preserves NULL and span validation while
removing the per-cell format test. -/
@[inline] def decodePlannedBuiltinBinarySpanAt [Pg.PgDecode α] [Pg.PgDecodeSpan α]
    (typeOid : UInt32) (row : @& Pg.Protocol.DataRowSpans)
    (index : Nat) (h : index < row.size) : Except Error α :=
  match Pg.decodeDataRowBinaryAt (α := α) typeOid row index h with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

/-- Decode a built-in text-format result after generated batch dispatch has
proved both that the column is present and that the prepared format is text.
The fixed-format pg-lean entry point preserves NULL, span, and UTF-8 validation
while removing the per-cell format test. -/
@[inline] def decodePlannedBuiltinTextSpanAt [Pg.PgDecode α]
    (typeOid : UInt32) (row : @& Pg.Protocol.DataRowSpans)
    (index : Nat) (h : index < row.size) : Except Error α :=
  match Pg.decodeDataRowTextAt (α := α) typeOid row index h with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

/-- Selecting a prepared result's binary format once per batch changes neither
the decoded value nor PGX's exact `Error.decode` mapping. -/
theorem decodePlannedBuiltinBinarySpanAt_eq_decodePlannedBuiltinSpanAt
    [Pg.PgDecode α] [Pg.PgDecodeSpan α] (typeOid : UInt32)
    (row : Pg.Protocol.DataRowSpans) (index : Nat) (h : index < row.size) :
    decodePlannedBuiltinBinarySpanAt (α := α) typeOid row index h =
      decodePlannedBuiltinSpanAt (α := α) typeOid 1 row index h := by
  simp only [decodePlannedBuiltinBinarySpanAt, decodePlannedBuiltinSpanAt,
    Pg.decodeDataRowBinaryAt_eq_decodeDataRowValueAt]

/-- Selecting a prepared result's text format once per batch changes neither
the decoded value nor PGX's exact `Error.decode` mapping. -/
theorem decodePlannedBuiltinTextSpanAt_eq_decodePlannedBuiltinSpanAt
    [Pg.PgDecode α] [Pg.PgDecodeSpan α] (typeOid : UInt32)
    (row : Pg.Protocol.DataRowSpans) (index : Nat) (h : index < row.size) :
    decodePlannedBuiltinTextSpanAt (α := α) typeOid row index h =
      decodePlannedBuiltinSpanAt (α := α) typeOid 0 row index h := by
  simp only [decodePlannedBuiltinTextSpanAt, decodePlannedBuiltinSpanAt,
    Pg.decodeDataRowTextAt_eq_decodeDataRowValueAt]

/-- Supplying the generated row-width proof changes neither decoded values nor
the exact PGX error mapping. -/
theorem decodePlannedBuiltinSpanAt_eq_decodePlannedBuiltinSpan
    [Pg.PgDecode α] [Pg.PgDecodeSpan α] (typeOid : UInt32) (format : UInt16)
    (row : Pg.Protocol.DataRowSpans) (index : Nat) (h : index < row.size) :
    decodePlannedBuiltinSpanAt (α := α) typeOid format row index h =
      decodePlannedBuiltinSpan (α := α) typeOid format row index := by
  simp only [decodePlannedBuiltinSpanAt, decodePlannedBuiltinSpan,
    Pg.decodeDataRowValueAt_eq_decodeDataRowValue]

/-- Encode through a generated codec using its already-resolved outer
parameter descriptor.  The connection plan has already matched the descriptor
to the generated spec; avoiding another full static-descriptor comparison is
part of the planned path.  The resolver remains available for genuine nested
container dependencies. -/
def encodePlanned (codec : ResolvedCodec α) (resolve : TypeResolver)
    (resolved : ResolvedType) (value : α) : Except Error EncodedValue :=
  codec.encode resolve resolved value

/-- Decode through a generated codec using its already-resolved outer result
descriptor.  The spec/plan association has already been checked on the cache
path; nested container dependencies may still use `resolve`. -/
def decodePlanned (codec : ResolvedCodec α) (resolve : TypeResolver)
    (resolved : ResolvedType) (format : UInt16) (value : Option ByteArray) :
    Except Error α :=
  codec.decode resolve resolved format value

/-- Physical origin recorded once from a checked catalog. -/
structure PhysicalColumnOrigin where
  tableOid : UInt32
  attnum : UInt16
  deriving Repr, BEq, Inhabited

/-- Numeric portal-validation expectation.  It contains no symbolic type or
relation keys, so validating a hot execution cannot scan the catalog. -/
structure PreparedColumnPlan where
  name : String
  typeOid : UInt32
  typeMod : Int32
  origin : Option PhysicalColumnOrigin := none
  format : UInt16 := 0
  deriving Repr, BEq, Inhabited

/-- Everything reusable after a query has been prepared and checked on one
physical connection.  Values of this type are retained only in that checked
connection's private cache. -/
structure PreparedQueryPlan (db : DatabaseDesc) where
  cacheKey : String
  contractHash : String
  statement : Pg.Statement
  params : Array ResolvedType
  results : Array ResolvedType
  /-- Connection-local resolver retained for nested container codecs.  Direct
  parameter/result descriptors use the arrays above and never call it. -/
  resolve : TypeResolver
  columns : Array PreparedColumnPlan
  /-- Validated Bind result-format vector, retained in its compact PostgreSQL
  representation (empty, one entry, or one per result). -/
  resultFormats : Array UInt16
  deriving Inhabited

/-- Preserve the established malformed-row diagnostic at both the single-row
and generated batch-decoder boundaries. -/
@[inline] def dataRowArityError (actual expected : Nat) : Error :=
  .queryDrift s!"data row has {actual} fields; expected {expected}"

abbrev PreparedSpanRowDecoder (Row : Type) :=
  TypeResolver → Array ResolvedType → Array Pg.Protocol.ColumnDesc →
    Pg.Protocol.DataRowSpans → Except Error Row

abbrev PreparedSpanBatchDecoder (Row : Type) :=
  TypeResolver → Array ResolvedType → Array Pg.Protocol.ColumnDesc →
    Array Pg.Protocol.DataRowSpans → Except Error (Array Row)

/-- Decode retained rows left-to-right after preserving the public dynamic
row-arity guard and its exact error. -/
abbrev guardedPreparedSpanRows (expectedColumns : Nat)
    (decode : PreparedSpanRowDecoder Row) (resolve : TypeResolver)
    (types : Array ResolvedType) (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  rows.mapM fun values =>
    if values.size = expectedColumns then
      decode resolve types columns values
    else
      throw (dataRowArityError values.size expectedColumns)

/-- A generated retained-span decoder and its proof-equivalent batch path.
The explicit expected count keeps ordinary `QuerySpec` record updates
source-compatible; the runtime checks it once before selecting `many`. -/
structure PreparedSpanDecoderBundle (Row : Type) where
  expectedColumns : Nat
  row : PreparedSpanRowDecoder Row
  many : PreparedSpanBatchDecoder Row
  many_eq_guardedRow : ∀ resolve types columns rows,
    many resolve types columns rows =
      guardedPreparedSpanRows expectedColumns row resolve types columns rows

structure QuerySpec (db : DatabaseDesc) (Params Row : Type)
    (cardinality : Pgx.Cardinality) where
  name : String
  sql : String
  /-- Stable query-contract fingerprint.  Manual specs that share a cache key
  must use the same value only when their parameter/result/format contract is
  identical. -/
  contractHash : String
  /-- Generation-time `queryCacheKey`. The empty default preserves manually
  authored source compatibility; generated specs always embed a nonempty key,
  while legacy/manual specs derive it on demand.  Supplying a nonempty manual
  value asserts that it is the full database-contract/query-contract/SQL
  identity, not merely a PostgreSQL statement name. -/
  cacheKey : String := ""
  params : Array ParamSpec
  columns : Array ColumnSpec
  /-- Bind result formats using PostgreSQL's shorthand: empty means all text,
  one entry applies to every result column, and otherwise there is one entry
  per column.  The empty compatibility default preserves the prior text path. -/
  resultFormats : Array UInt16 := #[]
  encode : ResolvedCatalog db → Params → Except Error EncodedParams
  decode : ResolvedCatalog db → Array Pg.Protocol.ColumnDesc →
    Array (Option ByteArray) → Except Error Row
  /-- Generated fast path.  The outer parameter descriptors have already been
  resolved by the connection-bound prepared plan; `TypeResolver` is retained
  only for nested codec dependencies. -/
  preparedEncode : Option (TypeResolver → Array ResolvedType → Params →
    Except Error EncodedParams) := none
  /-- Generated fast path using result descriptors resolved once with the
  prepared statement. -/
  preparedDecode : Option (TypeResolver → Array ResolvedType →
    Array Pg.Protocol.ColumnDesc → Array (Option ByteArray) →
    Except Error Row) := none
  /-- Generated prepared path that retains one backend payload per row.  A
  missing callback preserves manual-spec compatibility by materializing the
  row and using `preparedDecode`/`decode`. -/
  preparedSpanDecode : Option (TypeResolver → Array ResolvedType →
    Array Pg.Protocol.ColumnDesc → Pg.Protocol.DataRowSpans →
    Except Error Row) := none
  /-- Generated `.many` path that may cache checked result descriptors once per
  batch.  The trailing default preserves record-literal compatibility for
  legacy and manually authored specs. -/
  preparedSpanDecoderBundle :
    Option (PreparedSpanDecoderBundle Row) := none

/-- Resolve the parameter descriptors once before Parse. -/
def resolvePreparedParams (catalog : ResolvedCatalog db)
    (params : Array ParamSpec) : Except Error (Array ResolvedType) :=
  params.mapM fun param => catalog.resolveType param.ty.key

private def physicalOrigin (catalog : ResolvedCatalog db)
    (columnName : String) (origin : Pgx.ColumnKey) : Except Error PhysicalColumnOrigin := do
  let some relation := catalog.resolveRelation? origin.relation
    | throw (.queryDrift
        s!"result column {columnName} has an unresolved symbolic origin")
  let some column := relation.columns.find? (fun value =>
      value.expected.name == origin.name)
    | throw (.queryDrift
        s!"result column {columnName} has an unresolved symbolic origin")
  pure { tableOid := relation.oid, attnum := column.attnum }

private def expandedResultFormats (columnCount : Nat)
    (formats : Array UInt16) : Except Error (Array UInt16) := do
  unless formats.isEmpty || formats.size == 1 || formats.size == columnCount do
    throw (.queryDrift
      s!"result format vector has {formats.size} entries; expected 0, 1, or {columnCount}")
  for format in formats do
    unless format == 0 || format == 1 do
      throw (.queryDrift s!"unsupported PostgreSQL result format {format}")
  if formats.isEmpty then
    pure (Array.replicate columnCount 0)
  else if formats.size == 1 then
    pure (Array.replicate columnCount formats[0]!)
  else
    pure formats

private def verifyPreparedColumnsReference (expected : Array PreparedColumnPlan)
    (actual : Array Pg.Protocol.ColumnDesc) (checkFormat : Bool) :
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
    unless got.typeOid == want.typeOid do
      throw (.queryDrift
        s!"result column {want.name} changed PostgreSQL type")
    unless got.typeMod == want.typeMod do
      throw (.queryDrift
        s!"result column {want.name} changed type modifier")
    match want.origin with
    | some origin =>
      unless got.tableOid == origin.tableOid && got.attnum == origin.attnum do
        throw (.queryDrift
          s!"result column {want.name} changed symbolic origin")
    | none => pure ()
    if checkFormat then
      unless got.format == want.format do
        throw (.queryDrift
          s!"result column {want.name} changed wire format")

private def verifyPreparedColumnsCandidateLoop
    (expected : @& Array PreparedColumnPlan)
    (actual : @& Array Pg.Protocol.ColumnDesc) (checkFormat : Bool)
    (limit index : USize) (expectedLimitBound : limit.toNat ≤ expected.size)
    (actualLimitBound : limit.toNat ≤ actual.size) (indexBound : index ≤ limit) :
    Except Error Unit := do
  if atEnd : index = limit then
    pure ()
  else
    have indexLt : index < limit :=
      USize.lt_iff_le_and_ne.mpr ⟨indexBound, atEnd⟩
    have expectedBound : index.toNat < expected.size :=
      Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp indexLt) expectedLimitBound
    have actualBound : index.toNat < actual.size :=
      Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp indexLt) actualLimitBound
    let want := expected.uget index expectedBound
    let got := actual.uget index actualBound
    unless got.name == want.name do
      throw (.queryDrift
        s!"result column {index.toNat + 1} changed name from {want.name} to {got.name}")
    unless got.typeOid == want.typeOid do
      throw (.queryDrift
        s!"result column {want.name} changed PostgreSQL type")
    unless got.typeMod == want.typeMod do
      throw (.queryDrift
        s!"result column {want.name} changed type modifier")
    match want.origin with
    | some origin =>
      unless got.tableOid == origin.tableOid && got.attnum == origin.attnum do
        throw (.queryDrift
          s!"result column {want.name} changed symbolic origin")
    | none => pure ()
    if checkFormat then
      unless got.format == want.format do
        throw (.queryDrift
          s!"result column {want.name} changed wire format")
    let next := index + 1
    have nextToNat : next.toNat = index.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
      exact Nat.lt_of_le_of_lt
        (Nat.succ_le_of_lt (USize.lt_iff_toNat_lt.mp indexLt))
        limit.toNat_lt_size
    have nextBound : next ≤ limit := by
      rw [USize.le_iff_toNat_le, nextToNat]
      exact USize.lt_iff_toNat_lt.mp indexLt
    verifyPreparedColumnsCandidateLoop expected actual checkFormat limit next
      expectedLimitBound actualLimitBound nextBound
termination_by limit.toNat - index.toNat
decreasing_by
  have stepToNat : (index + 1).toNat = index.toNat + 1 := by
    simpa only [next] using nextToNat
  rw [stepToNat]
  have := USize.lt_iff_toNat_lt.mp indexLt
  omega

private def verifyPreparedColumnsCandidate (expected : Array PreparedColumnPlan)
    (actual : Array Pg.Protocol.ColumnDesc) (checkFormat : Bool) :
    Except Error Unit :=
  if sizeEq : actual.size = expected.size then
    -- Lean's array executor guarantees representable runtime sizes are
    -- strictly below `USize.size`, so `Array.usize` covers the complete array.
    let limit := expected.usize
    let expectedLimitBound : limit.toNat ≤ expected.size := by
      simp only [limit, Array.usize, Nat.toUSize_eq, USize.toNat_ofNat']
      exact Nat.mod_le _ _
    let actualLimitBound : limit.toNat ≤ actual.size := by
      simpa only [sizeEq] using expectedLimitBound
    let indexBound : (0 : USize) ≤ limit := by
      rw [USize.le_iff_toNat_le, USize.toNat_zero]
      exact Nat.zero_le _
    verifyPreparedColumnsCandidateLoop expected actual checkFormat limit 0
      expectedLimitBound actualLimitBound indexBound
  else
    .error (.queryDrift
      s!"result column count changed from {expected.size} to {actual.size}")

namespace PreparedColumnVerificationBenchmark

/-- Exact former logical verifier for semantic and counter differentials. -/
@[noinline] def verifyReference (expected : Array PreparedColumnPlan)
    (actual : Array Pg.Protocol.ColumnDesc) (checkFormat : Bool) :
    Except Error Unit :=
  verifyPreparedColumnsReference expected actual checkFormat

/-- Exact compiled production verifier for semantic and counter differentials. -/
@[noinline] def verifyCandidate (expected : Array PreparedColumnPlan)
    (actual : Array Pg.Protocol.ColumnDesc) (checkFormat : Bool) :
    Except Error Unit :=
  verifyPreparedColumnsCandidate expected actual checkFormat

end PreparedColumnVerificationBenchmark

/-- The logical definition preserves the former Range-loop semantics exactly;
compiled production uses the proof-bounded native-index implementation. -/
@[implemented_by verifyPreparedColumnsCandidate]
private def verifyPreparedColumns (expected : Array PreparedColumnPlan)
    (actual : Array Pg.Protocol.ColumnDesc) (checkFormat : Bool) :
    Except Error Unit :=
  verifyPreparedColumnsReference expected actual checkFormat

/-- Finish a connection-bound plan after Parse/Describe has succeeded.  All
symbolic result types and origins are converted to physical descriptors here,
then both the statement's parameter description and row description are
checked before the plan can enter the ready cache state. -/
def createPreparedQueryPlan (catalog : ResolvedCatalog db) (cacheKey contractHash : String)
    (params : Array ParamSpec) (resolvedParams : Array ResolvedType)
    (columns : Array ColumnSpec) (resultFormats : Array UInt16)
    (statement : Pg.Statement) : Except Error (PreparedQueryPlan db) := do
  unless resolvedParams.size == params.size do
    throw (.queryDrift
      s!"resolved parameter plan has {resolvedParams.size} entries; expected {params.size}")
  unless statement.paramTypes.size == params.size do
    throw (.queryDrift
      s!"parameter count changed from {params.size} to {statement.paramTypes.size}")
  for i in [0:params.size] do
    let resolved := resolvedParams[i]!
    unless resolved.expected.key == params[i]!.ty.key do
      throw (.queryDrift s!"resolved parameter {i + 1} changed symbolic type")
    unless statement.paramTypes[i]! == resolved.oid do
      throw (.queryDrift s!"parameter {i + 1} changed PostgreSQL type")
  let formats ← expandedResultFormats columns.size resultFormats
  let mut results : Array ResolvedType := #[]
  let mut preparedColumns : Array PreparedColumnPlan := #[]
  for i in [0:columns.size] do
    let column := columns[i]!
    let resolved ← match catalog.resolveType column.ty.key with
      | .ok value => pure value
      | .error _ => throw (.queryDrift
          s!"result column {column.name} has an unresolved symbolic type")
    results := results.push resolved
    let origin ← column.origin.mapM (physicalOrigin catalog column.name)
    preparedColumns := preparedColumns.push {
      name := column.name
      typeOid := resolved.oid
      typeMod := column.ty.typmod.getD (-1)
      origin
      format := formats[i]!
    }
  verifyPreparedColumns preparedColumns statement.columns false
  pure {
    cacheKey
    contractHash
    statement
    params := resolvedParams
    results
    resolve := fun key => catalog.resolveType key
    columns := preparedColumns
    resultFormats
  }

/-- Constant-time defense against handing a ready plan to a different query
contract.  Generated cache identities already bind the database contract,
query contract, and SQL.  A manual nonempty `cacheKey` is therefore an
assertion that those inputs are identical; lying about both it and
`contractHash` is a malformed manual contract, just like supplying an invalid
encoder callback.  Sizes additionally protect planned array indexing without
rescanning symbolic descriptors on every hit. -/
def verifyPreparedQueryIdentity (plan : PreparedQueryPlan db)
    (cacheKey contractHash : String) (paramCount columnCount formatCount : Nat) :
    Except Error Unit := do
  unless plan.cacheKey == cacheKey && plan.contractHash == contractHash do
    throw (.queryDrift
      "prepared query cache identity aliases a different query contract")
  unless plan.params.size == paramCount do
    throw (.queryDrift
      "prepared query cache identity aliases a different parameter shape")
  unless plan.results.size == columnCount do
    throw (.queryDrift
      "prepared query cache identity aliases a different result shape")
  unless plan.resultFormats.size == formatCount do
    throw (.queryDrift
      "prepared query cache identity aliases a different result-format shape")

/-- Validate each portal RowDescription against the cached numeric plan.  This
remains on every execution and runs before any generated decoder. -/
def verifyPreparedResultColumns (plan : PreparedQueryPlan db)
    (actual : Array Pg.Protocol.ColumnDesc) : Except Error Unit :=
  verifyPreparedColumns plan.columns actual true

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
    (expected : Array ColumnSpec) (actual : Array Pg.Protocol.ColumnDesc)
    (formats : Array UInt16 := #[]) : Except Error Unit := do
  verifyColumns catalog expected actual
  unless formats.isEmpty || formats.size == 1 || formats.size == expected.size do
    throw (.queryDrift
      s!"result format vector has {formats.size} entries; expected 0, 1, or {expected.size}")
  for i in [0:expected.size] do
    let want : UInt16 := if formats.isEmpty then 0
      else if formats.size == 1 then formats[0]!
      else formats[i]!
    unless want == 0 || want == 1 do
      throw (.queryDrift s!"unsupported PostgreSQL result format {want}")
    unless actual[i]!.format == want do
      throw (.queryDrift
        s!"result column {expected[i]!.name} changed wire format")

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
