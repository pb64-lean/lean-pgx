import Pgx.TypeMapping
import Pgx.Codegen.ConstraintParser
import Pgx.Codegen.Projection
import Pgx.Codegen.Probe.Pg17
import Pgx.Codegen.Probe.Pg18
import Pg.Connection
import Lean.Data.Json

/-!
# PostgreSQL generation probe

This module runs after migrations have been applied to an already-connected
server.  Catalog OIDs are retained only in private, transient lookup records;
the public result is the symbolic `Pgx.DatabaseIR` consumed by source
generation.
-/

namespace Pgx.Codegen.Probe

open Std.Async

/-- Parameter facts PostgreSQL cannot infer from a parsed statement. -/
structure ParameterInput where
  /-- One-based PostgreSQL parameter position. -/
  position : Nat
  name : String
  nullable : Bool
  deriving Repr, BEq, Inhabited

/-- One literal SQL source and its non-SQL contract metadata. -/
structure QueryInput where
  name : String
  sql : String
  cardinality : Pgx.Cardinality
  parameters : Array ParameterInput := #[]
  deriving Repr, BEq, Inhabited

/-- Manifest-neutral provenance for a reusable extension codec package.
Installed extension versions are deliberately absent here and are resolved
from `pg_extension` while probing the migrated database. -/
structure ExtensionCodecPackageInput where
  extension : String
  importModule : String
  types : Array Pgx.TypeKey
  deriving Repr, BEq, Inhabited

/-- Inputs which affect the normalized database contract.  The connection is
expected to point at an empty-cluster migration result owned by the caller. -/
structure Config where
  schemas : Array String
  session : Pgx.SessionContract
  queries : Array QueryInput := #[]
  supportedServerMajors : Array Nat := #[17, 18]
  requiredExtensions : Array String := #[]
  typeOverrides : Array Pgx.TypeOverrideIR := #[]
  extensionCodecPackages : Array ExtensionCodecPackageInput := #[]
  deriving Repr, BEq, Inhabited

namespace Config

/-- Canonical server-major set copied into the generated database contract. -/
def normalizedSupportedServerMajors (config : Config) : Array Nat :=
  config.supportedServerMajors.toList.mergeSort (· < ·) |>.toArray

end Config

/-- Select the catalog adapter from the live server's reported major. -/
def adapterForServerMajor? : Nat → Option Adapter
  | 17 => some Pg17.adapter
  | 18 => some Pg18.adapter
  | _ => none

inductive Error where
  | invalidConfig (message : String)
  | postgres (context : String) (error : Pg.Error)
  | catalog (message : String)
  | invalidQuery (query : String) (message : String)
  | unsupportedType (context : String) (key : Pgx.TypeKey)
  | unsupportedConstraint (owner name source : String)
      (diagnostic : Pgx.Constraint.Diagnostic)
  deriving Repr

namespace Error

def toMessage : Error → String
  | .invalidConfig message => s!"invalid probe configuration: {message}"
  | .postgres context error => s!"{context}: {error}"
  | .catalog message => s!"invalid PostgreSQL catalog result: {message}"
  | .invalidQuery query message => s!"query {query}: {message}"
  | .unsupportedType context key =>
      s!"{context}: unsupported PostgreSQL type {key}"
  | .unsupportedConstraint owner name source diagnostic =>
      s!"constraint {owner}.{name}: category={diagnostic.category.tag}, \
        offset={diagnostic.offset}: {diagnostic.message}; source={repr source}"

end Error

instance : ToString Error := ⟨Error.toMessage⟩

/-- Reject functions and operators for which `pg_constraint` records a
dependency.  PostgreSQL's pinned built-ins do not acquire these dependency
rows; ordinary and extension objects do, regardless of their schema. -/
def validateLocalConstraintDependencies (owner name source : String)
    (functionDependency operatorDependency : Bool) : Except Error Unit := do
  if functionDependency then
    throw (.unsupportedConstraint owner name source {
      category := .unsupportedFunction
      offset := 0
      message := "catalog-dependent functions are unsupported in local constraints"
    })
  if operatorDependency then
    throw (.unsupportedConstraint owner name source {
      category := .unsupportedOperator
      offset := 0
      message := "catalog-dependent operators are unsupported in local constraints"
    })

/-- Check that `pg_get_constraintdef`'s `NOT VALID` suffix agrees with the
authoritative catalog bit instead of silently accepting a deparse mismatch. -/
def validateConstraintValidationMetadata (owner name : String)
    (catalogValidated parsedValidated : Bool) : Except Error Unit := do
  unless parsedValidated == catalogValidated do
    throw (.catalog s!"constraint {owner}.{name}: pg_get_constraintdef validation suffix \
      implies convalidated={parsedValidated}, but pg_constraint reports \
      convalidated={catalogValidated}")

/-- Result of the deliberately one-sided plan inspection.  Both `outerJoin`
and `uncertain` force every result field back to nullable. -/
inductive OuterJoinAnalysis where
  | noOuterJoin
  | outerJoin
  | uncertain
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Conservative facts recovered from one fully recognized generic plan.
`rowPreservedRelations` contains only base relations with exactly one scan
occurrence and is empty whenever an outer join is present or analysis is
uncertain. -/
structure QueryPlanAnalysis where
  outerJoins : OuterJoinAnalysis
  rowPreservedRelations : Array Pgx.RelationKey := #[]
  deriving Repr, BEq, Inhabited

private def sqlLiteral (value : String) : String :=
  "'" ++ value.replace "'" "''" ++ "'"

private def sqlIdentifier (value : String) : String :=
  "\"" ++ value.replace "\"" "\"\"" ++ "\""

private def isSpace : Char → Bool
  | ' ' | '\t' | '\r' | '\n' => true
  | _ => false

private def isBlank (value : String) : Bool :=
  value.toList.all isSpace

private def hasDuplicates [BEq α] (values : Array α) : Bool := Id.run do
  let mut seen : Array α := #[]
  for value in values do
    if seen.contains value then return true
    seen := seen.push value
  return false

private def queryOne (conn : Pg.Connection) (context sql : String) :
    Async (Except Error Pg.Rows) := do
  match ← Pg.Connection.query conn sql with
  | .error error => pure (.error (.postgres context error))
  | .ok results =>
    match results with
    | #[rows] => pure (.ok rows)
    | _ => pure (.error (.catalog
        s!"{context}: expected one result set, received {results.size}"))

private def cell? (context : String) (row : Array (Option ByteArray))
    (index : Nat) : Except Error (Option String) := do
  let some value := row[index]?
    | throw (.catalog s!"{context}: result row has no column {index}")
  match value with
  | none => pure none
  | some bytes =>
    let some value := String.fromUTF8? bytes
      | throw (.catalog s!"{context}: result column {index} is not UTF-8")
    pure (some value)

private def cell (context : String) (row : Array (Option ByteArray))
    (index : Nat) : Except Error String := do
  let some value ← cell? context row index
    | throw (.catalog s!"{context}: result column {index} is NULL")
  pure value

private def parseNat (context value : String) : Except Error Nat := do
  let some parsed := value.toNat?
    | throw (.catalog s!"{context}: expected an unsigned integer, received {value}")
  pure parsed

private def parseUInt32 (context value : String) : Except Error UInt32 := do
  let parsed ← parseNat context value
  if parsed < 4294967296 then
    pure (UInt32.ofNat parsed)
  else
    throw (.catalog s!"{context}: value is outside the UInt32 range: {value}")

private def parseUInt16 (context value : String) : Except Error UInt16 := do
  let parsed ← parseNat context value
  if parsed < 65536 then
    pure (UInt16.ofNat parsed)
  else
    throw (.catalog s!"{context}: value is outside the UInt16 range: {value}")

private def parseInt32 (context value : String) : Except Error Int32 := do
  let some parsed := value.toInt?
    | throw (.catalog s!"{context}: expected an integer, received {value}")
  if (-2147483648 : Int) ≤ parsed ∧ parsed ≤ 2147483647 then
    pure (Int32.ofInt parsed)
  else
    throw (.catalog s!"{context}: value is outside the Int32 range: {value}")

private def parseBool (context : String) : String → Except Error Bool
  | "t" | "true" | "on" => pure true
  | "f" | "false" | "off" => pure false
  | value => throw (.catalog s!"{context}: expected a boolean, received {value}")

private def parseTypeKind (context : String) : String → Except Error Pgx.TypeKind
  | "base" => pure .base
  | "enum" => pure .enum
  | "domain" => pure .domain
  | "array" => pure .array
  | "range" => pure .range
  | "multirange" => pure .multirange
  | "composite" => pure .composite
  | "pseudo" => pure .pseudo
  | value => throw (.catalog s!"{context}: unknown type kind {value}")

private def parseRelationKind (context : String) : String → Except Error Pgx.RelationKind
  | "r" => pure .table
  | "p" => pure .partitionedTable
  | "v" => pure .view
  | "m" => pure .materializedView
  | "f" => pure .foreignTable
  | value => throw (.catalog s!"{context}: unknown relation kind {value}")

private def parseRoutineKind (context : String) : String → Except Error Pgx.RoutineKind
  | "f" => pure .function
  | "p" => pure .procedure
  | "a" => pure .aggregate
  | "w" => pure .window
  | value => throw (.catalog s!"{context}: unknown routine kind {value}")

private def parseRoutineArgMode (context : String) : String →
    Except Error Pgx.RoutineArgMode
  | "i" => pure .input
  | "o" => pure .output
  | "b" => pure .inputOutput
  | "v" => pure .variadic
  | "t" => pure .table
  | value => throw (.catalog s!"{context}: unknown routine argument mode {value}")

private def parseConstraintKind (adapter : Adapter) (context value : String) :
    Except Error Pgx.ConstraintKind :=
  match adapter.constraintKind? value with
  | some kind => pure kind
  | none => throw (.catalog
      s!"{context}: PostgreSQL {adapter.serverMajor} adapter does not support \
        constraint kind {value}")

private def parseForeignKeyMatch (context : String) : String →
    Except Error Pgx.ForeignKeyMatch
  | "s" => pure .simple
  | "f" => pure .full
  | "p" => pure .partialMatch
  | value => throw (.catalog s!"{context}: unknown foreign-key match type {value}")

private def parseForeignKeyAction (context : String) : String →
    Except Error Pgx.ForeignKeyAction
  | "a" => pure .noAction
  | "r" => pure .restrict
  | "c" => pure .cascade
  | "n" => pure .setNull
  | "d" => pure .setDefault
  | value => throw (.catalog s!"{context}: unknown foreign-key action {value}")

private def kindSql (alias : String) : String :=
  s!"CASE WHEN {alias}.typcategory = 'A' AND {alias}.typelem <> 0 \
     AND {alias}.typinput = 'pg_catalog.array_in'::pg_catalog.regproc \
     AND {alias}.typoutput = 'pg_catalog.array_out'::pg_catalog.regproc \
     AND {alias}.typreceive = 'pg_catalog.array_recv'::pg_catalog.regproc \
     AND {alias}.typsend = 'pg_catalog.array_send'::pg_catalog.regproc THEN 'array' \
     WHEN {alias}.typtype = 'b' THEN 'base' \
     WHEN {alias}.typtype = 'c' THEN 'composite' \
     WHEN {alias}.typtype = 'd' THEN 'domain' \
     WHEN {alias}.typtype = 'e' THEN 'enum' \
     WHEN {alias}.typtype = 'p' THEN 'pseudo' \
     WHEN {alias}.typtype = 'r' THEN 'range' \
     WHEN {alias}.typtype = 'm' THEN 'multirange' ELSE 'pseudo' END"

private def setConfig (conn : Pg.Connection) (name value : String) :
    Async (Except Error Unit) := do
  let sql := s!"SELECT pg_catalog.set_config({sqlLiteral name}, {sqlLiteral value}, false)"
  match ← queryOne conn s!"set session parameter {name}" sql with
  | .error error => pure (.error error)
  | .ok rows =>
    if rows.rows.size == 1 then pure (.ok ())
    else pure (.error (.catalog
      s!"set session parameter {name}: expected one row, received {rows.rows.size}"))

private def currentSetting (conn : Pg.Connection) (name : String) :
    Async (Except Error String) := do
  match ← queryOne conn s!"read session parameter {name}"
      s!"SELECT pg_catalog.current_setting({sqlLiteral name})" with
  | .error error => pure (.error error)
  | .ok rows =>
    let some row := rows.rows[0]?
      | return .error (.catalog s!"read session parameter {name}: no row returned")
    if rows.rows.size != 1 then
      return .error (.catalog
        s!"read session parameter {name}: expected one row, received {rows.rows.size}")
    pure (cell s!"read session parameter {name}" row 0)

/-- Validate and install the session settings which are later fingerprinted. -/
def configureSession (conn : Pg.Connection) (session : Pgx.SessionContract) :
    Async (Except Error Unit) := do
  if session.searchPath.isEmpty then
    return .error (.invalidConfig "session search_path must not be empty")
  if hasDuplicates session.searchPath then
    return .error (.invalidConfig "session search_path contains duplicates")
  if session.searchPath.any isBlank then
    return .error (.invalidConfig "session search_path contains an empty schema")
  unless session.encoding.toUpper == "UTF8" do
    return .error (.invalidConfig "generated contracts require UTF8 client encoding")
  if isBlank session.timezone then
    return .error (.invalidConfig "session timezone must not be empty")
  let searchPath := String.intercalate ", "
    (session.searchPath.map sqlIdentifier).toList
  for (name, value) in #[
      ("search_path", searchPath),
      ("TimeZone", session.timezone),
      ("client_encoding", session.encoding),
      ("standard_conforming_strings",
        if session.standardConformingStrings then "on" else "off")] do
    match ← setConfig conn name value with
    | .error error => return .error error
    | .ok () => pure ()
  match ← currentSetting conn "TimeZone" with
  | .error error => return .error error
  | .ok actual =>
    unless actual == session.timezone do
      return .error (.invalidConfig
        s!"PostgreSQL canonicalized timezone {session.timezone} to {actual}; \
          use the canonical value in the session contract")
  match ← currentSetting conn "client_encoding" with
  | .error error => return .error error
  | .ok actual =>
    unless actual.toUpper == session.encoding.toUpper do
      return .error (.catalog
        s!"client_encoding is {actual}, expected {session.encoding}")
  match ← currentSetting conn "standard_conforming_strings" with
  | .error error => return .error error
  | .ok actual =>
    match parseBool "standard_conforming_strings" actual with
    | .error error => return .error error
    | .ok enabled =>
      unless enabled == session.standardConformingStrings do
        return .error (.catalog
          s!"standard_conforming_strings is {actual}, expected \
            {session.standardConformingStrings}")
  match ← queryOne conn "read effective search_path"
      "SELECT schema_name FROM pg_catalog.unnest(pg_catalog.current_schemas(false)) \
       WITH ORDINALITY AS path(schema_name, ordinal) ORDER BY ordinal" with
  | .error error => return .error error
  | .ok rows =>
    let mut actual : Array String := #[]
    for row in rows.rows do
      match cell "read effective search_path" row 0 with
      | .error error => return .error error
      | .ok schema => actual := actual.push schema
    unless actual == session.searchPath do
      return .error (.invalidConfig
        s!"effective search_path is {repr actual}, expected {repr session.searchPath}; \
          list pg_catalog explicitly and remove missing schemas")
  pure (.ok ())

private def validateParameterInput (query : QueryInput) : Except Error Unit := do
  let ordered := query.parameters.toList.mergeSort
    (fun left right => left.position < right.position) |>.toArray
  let mut names : Array String := #[]
  for index in [:ordered.size] do
    let parameter := ordered[index]!
    unless parameter.position == index + 1 do
      throw (.invalidQuery query.name
        s!"parameter positions must be dense and one-based; expected {index + 1}, \
          received {parameter.position}")
    if isBlank parameter.name then
      throw (.invalidQuery query.name
        s!"parameter {parameter.position} has an empty name")
    if names.contains parameter.name then
      throw (.invalidQuery query.name
        s!"parameter name {parameter.name} is duplicated")
    names := names.push parameter.name

/-- Pure validation useful to manifest readers before a connection is opened. -/
def validateConfig (config : Config) : Except Error Unit := do
  if config.schemas.isEmpty then
    throw (.invalidConfig "at least one generated schema is required")
  if config.schemas.any isBlank then
    throw (.invalidConfig "generated schema names must not be empty")
  if hasDuplicates config.schemas then
    throw (.invalidConfig "generated schema names contain duplicates")
  if config.supportedServerMajors.isEmpty then
    throw (.invalidConfig "supportedServerMajors must not be empty")
  if hasDuplicates config.supportedServerMajors then
    throw (.invalidConfig "supportedServerMajors contains duplicates")
  for major in config.supportedServerMajors do
    if (adapterForServerMajor? major).isNone then
      throw (.invalidConfig s!"PostgreSQL major {major} has no probe adapter")
  if config.requiredExtensions.any isBlank then
    throw (.invalidConfig "required extension names must not be empty")
  if hasDuplicates config.requiredExtensions then
    throw (.invalidConfig "required extension names contain duplicates")
  if hasDuplicates (config.typeOverrides.map (·.key)) then
    throw (.invalidConfig "type override keys contain duplicates")
  for override in config.typeOverrides do
    if isBlank override.leanType || isBlank override.codec then
      throw (.invalidConfig s!"type override {override.key} has an empty Lean type or codec")
  if hasDuplicates (config.extensionCodecPackages.map (·.extension)) then
    throw (.invalidConfig "extension codec package names contain duplicates")
  let packagedTypes := config.extensionCodecPackages.flatMap (·.types)
  if hasDuplicates packagedTypes then
    throw (.invalidConfig "extension codec package type keys contain duplicates")
  for package in config.extensionCodecPackages do
    if isBlank package.extension ||
        package.extension.trimAscii.toString != package.extension then
      throw (.invalidConfig
        "extension codec package names must not be empty or untrimmed")
    if isBlank package.importModule ||
        package.importModule.trimAscii.toString != package.importModule then
      throw (.invalidConfig s!"extension codec package {package.extension} has an empty or untrimmed import module")
    if package.types.isEmpty then
      throw (.invalidConfig s!"extension codec package {package.extension} has no type overrides")
    unless config.requiredExtensions.contains package.extension do
      throw (.invalidConfig s!"extension codec package {package.extension} is not a required extension")
    for key in package.types do
      if isBlank key.schema || key.schema.trimAscii.toString != key.schema ||
          isBlank key.name || key.name.trimAscii.toString != key.name then
        throw (.invalidConfig s!"extension codec package {package.extension} has an empty or untrimmed type key")
      let some override := config.typeOverrides.find? (fun value => value.key == key)
        | throw (.invalidConfig s!"extension codec package {package.extension} type {key} has no resolved override")
      unless override.importModule == some package.importModule do
        throw (.invalidConfig s!"extension codec package {package.extension} type {key} does not use import module {package.importModule}")
  let mut queryNames : Array String := #[]
  for query in config.queries do
    if isBlank query.name then
      throw (.invalidConfig "query names must not be empty")
    if queryNames.contains query.name then
      throw (.invalidConfig s!"query name {query.name} is duplicated")
    if isBlank query.sql then
      throw (.invalidQuery query.name "SQL source is empty")
    validateParameterInput query
    queryNames := queryNames.push query.name

private def typeKeyLess (left right : Pgx.TypeKey) : Bool :=
  let leftKey := s!"{left.schema}\u0000{left.name}\u0000{left.kind.tag}"
  let rightKey := s!"{right.schema}\u0000{right.name}\u0000{right.kind.tag}"
  leftKey < rightKey

/-- Attach live installed versions to validated package declarations.  The
result is canonical even when callers supply package or type keys in a
different order. -/
def Config.resolvedExtensionCodecPackages (config : Config)
    (installed : Array (String × String)) : Except Error (Array Pgx.ExtensionCodecPackageIR) := do
  let mut result : Array Pgx.ExtensionCodecPackageIR := #[]
  for package in config.extensionCodecPackages do
    let some extension := installed.find? (fun value => value.1 == package.extension)
      | throw (.catalog s!"required extension {package.extension} is not installed")
    result := result.push {
      extension := package.extension
      version := extension.2
      importModule := package.importModule
      types := package.types.toList.mergeSort typeKeyLess |>.toArray
    }
  pure <| result.toList.mergeSort (fun left right =>
    if left.extension == right.extension then
      left.importModule < right.importModule
    else left.extension < right.extension) |>.toArray

/-- Symbolic extension membership recovered from `pg_depend`.  The physical
type OID used during probing is deliberately absent from the public value. -/
structure ExtensionTypeOwnership where
  key : Pgx.TypeKey
  extension : String
  deriving Repr, BEq, Inhabited

/-- Require every configured override to resolve to exactly one live symbolic
type.  This prevents an override from bypassing support checks for a missing
or incorrectly classified type. -/
def validateLiveTypeOverrides (overrides : Array Pgx.TypeOverrideIR)
    (liveKeys : Array Pgx.TypeKey) : Except Error Unit := do
  for override in overrides do
    let candidates := liveKeys.filter (· == override.key)
    if candidates.isEmpty then
      throw (.catalog s!"type override {override.key} does not exist in pg_type")
    unless candidates.size == 1 do
      throw (.catalog s!"type override {override.key} is ambiguous in pg_type")

/-- Require each packaged codec type to be an extension member owned by the
claimed extension.  Other extension-owned types, notably generated array
wrappers, remain eligible for ordinary generated codecs. -/
def validateExtensionCodecOwnership
    (packages : Array ExtensionCodecPackageInput)
    (ownership : Array ExtensionTypeOwnership) : Except Error Unit := do
  for package in packages do
    for key in package.types do
      let candidates := ownership.filter (fun value => value.key == key)
      let some owner := candidates[0]?
        | throw (.catalog s!"extension codec type {key} is not an extension member")
      unless candidates.size == 1 do
        throw (.catalog s!"extension codec type {key} has ambiguous extension ownership")
      unless owner.extension == package.extension do
        throw (.catalog s!"extension codec type {key} belongs to extension \
          {owner.extension}, not {package.extension}")

private structure CatalogType where
  oid : UInt32
  key : Pgx.TypeKey
  base : Option Pgx.TypeRef
  elementOid : Option UInt32
  delimiter : String
  relationOid : Option UInt32
  notNull : Bool
  defaultExpr : Option String
  deriving Inhabited

private structure CatalogRelation where
  oid : UInt32
  ir : Pgx.RelationIR
  attnums : Array UInt16 := #[]
  attributeNotNull : Array Bool := #[]
  deriving Inhabited

private structure CatalogConstraint where
  oid : UInt32
  ir : Pgx.ConstraintIR
  localColumnOrdinal : Nat := 0
  referencedColumnOrdinal : Nat := 0
  /-- `conexclop`, kept separate until it can be aligned with the supporting
  index's normalized key elements. -/
  exclusionOperators : Array Pgx.OperatorKey := #[]
  deriving Inhabited

private structure CatalogIndex where
  oid : UInt32
  key : Pgx.IndexKey
  ir : Pgx.IndexIR
  deriving Inhabited

private structure CatalogRoutine where
  oid : UInt32
  returnTypeOid : UInt32
  inputCount : Nat
  defaultCount : Nat
  extensionOwned : Bool
  ir : Pgx.RoutineIR
  deriving Inhabited

private structure CatalogSnapshot where
  serverMajor : Nat
  schemas : Array Pgx.SchemaIR
  types : Array CatalogType
  enums : Array Pgx.EnumIR
  arrays : Array Pgx.ArrayIR
  domains : Array Pgx.DomainIR
  composites : Array Pgx.CompositeIR
  ranges : Array Pgx.RangeIR
  multiranges : Array Pgx.MultirangeIR
  relations : Array CatalogRelation
  views : Array Pgx.ViewIR
  routines : Array Pgx.RoutineIR
  constraints : Array Pgx.ConstraintIR
  indexes : Array Pgx.IndexIR
  extensions : Array (String × String)
  extensionTypeOwnership : Array ExtensionTypeOwnership

private def typeByOid? (types : Array CatalogType) (oid : UInt32) : Option CatalogType :=
  types.find? (fun value => value.oid == oid)

private partial def unwrapDomainBase (domains : Array Pgx.DomainIR)
    (context : String) (ref : Pgx.TypeRef) (seen : Array Pgx.TypeKey := #[]) :
    Except Error Pgx.TypeRef := do
  unless ref.key.kind == .domain do return ref
  if seen.contains ref.key then
    throw (.catalog s!"{context}: domain nesting cycle reaches {ref.key.display}")
  let some domain := domains.find? (fun domain => domain.key == ref.key)
    | throw (.catalog s!"{context}: missing metadata for domain {ref.key.display}")
  unwrapDomainBase domains context domain.base (seen.push ref.key)

/-- Recover the logical domain type of a descriptor-proven identity
projection. PostgreSQL describes a domain-valued cell using its recursively
unwrapped wire type. A direct origin with any other wire description is drift,
not permission to attach the domain brand. -/
def logicalTypeForDirectProjection (domains : Array Pgx.DomainIR)
    (queryName resultName : String) (source : Pgx.RelationColumnIR)
    (wire : Pgx.TypeRef) : Except Error (Option Pgx.TypeRef) := do
  unless source.ty.key.kind == .domain do return none
  let context := s!"result column {resultName} of query {queryName}"
  let base ← unwrapDomainBase domains context source.ty
  unless base == wire do
    throw (.invalidQuery queryName
      s!"direct domain projection {resultName} originates at {source.name} with logical \
        type {source.ty.key.display}, whose wire type is {base.key.display} \
        (typmod {repr base.typmod}); PostgreSQL described {wire.key.display} \
        (typmod {repr wire.typmod})")
  pure (some source.ty)

private def typeRefByOid (types : Array CatalogType) (context : String)
    (oid : UInt32) (typmod : Option Int32 := none) : Except Error Pgx.TypeRef := do
  let some value := typeByOid? types oid
    | throw (.catalog s!"{context}: OID {oid} does not identify a catalog type")
  pure { key := value.key, typmod }

private def operatorKeyByOperandOids (types : Array CatalogType)
    (context schema name : String) (leftOid rightOid : UInt32) :
    Except Error Pgx.OperatorKey := do
  let some left := typeByOid? types leftOid
    | throw (.catalog s!"{context}: operator {schema}.{name} has missing left type OID {leftOid}")
  let some right := typeByOid? types rightOid
    | throw (.catalog s!"{context}: operator {schema}.{name} has missing right type OID {rightOid}")
  pure { schema, name, leftType := left.key, rightType := right.key }

private def relationByKey? (relations : Array CatalogRelation)
    (key : Pgx.RelationKey) : Option CatalogRelation :=
  relations.find? (fun value => value.ir.key == key)

private def relationOrigin? (relations : Array CatalogRelation)
    (oid : UInt32) (attnum : UInt16) : Option (Pgx.ColumnKey × Pgx.RelationColumnIR) := do
  if oid == 0 || attnum == 0 then none else
  let relation ← relations.find? (fun value => value.oid == oid)
  let index ← relation.attnums.findIdx? (· == attnum)
  let column ← relation.ir.columns[index]?
  pure ({ relation := relation.ir.key, name := column.name }, column)

private def loadServerMajor (conn : Pg.Connection) : Async (Except Error Nat) := do
  match ← currentSetting conn "server_version_num" with
  | .error error => pure (.error error)
  | .ok value =>
    match parseNat "server_version_num" value with
    | .error error => pure (.error error)
    | .ok version => pure (.ok (version / 10000))

private def loadSchemas (conn : Pg.Connection) (wanted : Array String) :
    Async (Except Error (Array Pgx.SchemaIR)) := do
  match ← queryOne conn "read pg_namespace"
      "SELECT nspname FROM pg_catalog.pg_namespace ORDER BY nspname" with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut found : Array String := #[]
    for row in rows.rows do
      match cell "read pg_namespace" row 0 with
      | .error error => return .error error
      | .ok name => if wanted.contains name then found := found.push name
    for name in wanted do
      unless found.contains name do
        return .error (.catalog s!"configured schema {name} does not exist")
    pure (.ok (found.map fun name => ({ name } : Pgx.SchemaIR)))

private def typeCatalogSql : String :=
  "SELECT t.oid::text, ns.nspname, t.typname, " ++ kindSql "t" ++
  ", bns.nspname, bt.typname, CASE WHEN bt.oid IS NULL THEN NULL ELSE " ++
  kindSql "bt" ++ " END, " ++
  "CASE WHEN t.typtype = 'd' AND t.typtypmod <> -1 THEN t.typtypmod::text ELSE NULL END, " ++
  "t.typnotnull::text, t.typdefault, NULLIF(t.typelem, 0)::text, " ++
  "t.typdelim::text, NULLIF(t.typrelid, 0)::text " ++
  "FROM pg_catalog.pg_type AS t " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = t.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_type AS bt ON bt.oid = NULLIF(t.typbasetype, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS bns ON bns.oid = bt.typnamespace " ++
  "ORDER BY t.oid"

private def parseCatalogType (row : Array (Option ByteArray)) : Except Error CatalogType := do
  let context := "read pg_type"
  let oid ← parseUInt32 context (← cell context row 0)
  let schema ← cell context row 1
  let name ← cell context row 2
  let kind ← parseTypeKind context (← cell context row 3)
  let baseSchema ← cell? context row 4
  let baseName ← cell? context row 5
  let baseKind ← cell? context row 6
  let baseTypmod ← match ← cell? context row 7 with
    | none => pure none
    | some value => some <$> parseInt32 context value
  let base ← match baseSchema, baseName, baseKind with
    | none, none, none =>
      if baseTypmod.isNone then pure none
      else throw (.catalog s!"{context}: base typmod exists without a base type")
    | some schema, some name, some kind =>
      pure (some {
        key := { schema, name, kind := ← parseTypeKind context kind }
        typmod := baseTypmod
      })
    | _, _, _ => throw (.catalog s!"{context}: incomplete base type identity")
  let notNull ← parseBool context (← cell context row 8)
  let defaultExpr ← cell? context row 9
  let elementOid ← match ← cell? context row 10 with
    | none => pure none
    | some value => some <$> parseUInt32 context value
  let delimiter ← cell context row 11
  let relationOid ← match ← cell? context row 12 with
    | none => pure none
    | some value => some <$> parseUInt32 context value
  pure {
    oid, key := { schema, name, kind }, base, elementOid, delimiter,
    relationOid, notNull, defaultExpr
  }

private def loadTypes (conn : Pg.Connection) :
    Async (Except Error (Array CatalogType)) := do
  match ← queryOne conn "read pg_type" typeCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut values : Array CatalogType := #[]
    for row in rows.rows do
      match parseCatalogType row with
      | .error error => return .error error
      | .ok value =>
        if values.any (fun found => found.oid == value.oid) then
          return .error (.catalog s!"duplicate pg_type OID {value.oid}")
        values := values.push value
    pure (.ok values)

/-- Catalog query used to prove extension ownership of packaged codec types.
Array types created with an extension type may also appear; callers validate
only the explicitly packaged keys and leave those wrappers generated. -/
def extensionTypeOwnershipSql : String :=
  "SELECT dep.objid::text, ext.extname " ++
  "FROM pg_catalog.pg_depend AS dep " ++
  "JOIN pg_catalog.pg_extension AS ext ON ext.oid = dep.refobjid " ++
  "WHERE dep.classid = 'pg_catalog.pg_type'::pg_catalog.regclass " ++
  "AND dep.objsubid = 0 " ++
  "AND dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass " ++
  "AND dep.refobjsubid = 0 " ++
  "AND dep.deptype = 'e' " ++
  "ORDER BY dep.objid, ext.extname"

private def loadExtensionTypeOwnership (conn : Pg.Connection)
    (types : Array CatalogType) :
    Async (Except Error (Array ExtensionTypeOwnership)) := do
  match ← queryOne conn "read extension type ownership" extensionTypeOwnershipSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut ownership : Array ExtensionTypeOwnership := #[]
    for row in rows.rows do
      let parsed : Except Error ExtensionTypeOwnership := do
        let oid ← parseUInt32 "read extension type ownership"
          (← cell "read extension type ownership" row 0)
        let some ty := typeByOid? types oid
          | throw (.catalog s!"extension dependency refers to missing type OID {oid}")
        pure { key := ty.key, extension := ← cell "read extension type ownership" row 1 }
      match parsed with
      | .error error => return .error error
      | .ok value => ownership := ownership.push value
    pure (.ok ownership)

private def loadArrays (schemas : Array String) (types : Array CatalogType) :
    Except Error (Array Pgx.ArrayIR) := do
  let mut arrays : Array Pgx.ArrayIR := #[]
  for ty in types do
    if ty.key.kind == .array then
      let some elementOid := ty.elementOid
        | throw (.catalog s!"array type {ty.key} has no element type")
      let element ← typeRefByOid types s!"array {ty.key}" elementOid
      if schemas.contains ty.key.schema || (Pgx.builtinTypeMapping? element.key).isSome then
        arrays := arrays.push { key := ty.key, element, delimiter := ty.delimiter }
  pure arrays

private def compositeCatalogSql : String :=
  "SELECT t.oid::text, a.attname, a.attnum::text, a.atttypid::text, " ++
  "CASE WHEN a.atttypmod = -1 THEN NULL ELSE a.atttypmod::text END, " ++
  "cns.nspname, coll.collname " ++
  "FROM pg_catalog.pg_type AS t " ++
  "JOIN pg_catalog.pg_class AS c ON c.oid = t.typrelid AND c.reltype = t.oid " ++
  "JOIN pg_catalog.pg_attribute AS a ON a.attrelid = c.oid " ++
  "LEFT JOIN pg_catalog.pg_collation AS coll ON coll.oid = NULLIF(a.attcollation, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS cns ON cns.oid = coll.collnamespace " ++
  "WHERE t.typtype = 'c' AND t.typisdefined " ++
  "AND a.attnum > 0 AND NOT a.attisdropped " ++
  "ORDER BY t.oid, a.attnum"

private def loadComposites (conn : Pg.Connection) (schemas : Array String)
    (types : Array CatalogType) : Async (Except Error (Array Pgx.CompositeIR)) := do
  let mut composites : Array Pgx.CompositeIR := #[]
  for ty in types do
    if ty.key.kind == .composite && schemas.contains ty.key.schema then
      let some _ := ty.relationOid
        | return .error (.catalog s!"composite type {ty.key} has no backing relation")
      composites := composites.push { key := ty.key, fields := #[] }
  match ← queryOne conn "read composite pg_attribute" compositeCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    for row in rows.rows do
      let parsed : Except Error (UInt32 × Pgx.CompositeFieldIR) := do
        let typeOid ← parseUInt32 "read composite pg_attribute"
          (← cell "read composite pg_attribute" row 0)
        let name ← cell "read composite pg_attribute" row 1
        let ordinal ← parseNat "read composite pg_attribute"
          (← cell "read composite pg_attribute" row 2)
        let fieldTypeOid ← parseUInt32 "read composite pg_attribute"
          (← cell "read composite pg_attribute" row 3)
        let typmod ← match ← cell? "read composite pg_attribute" row 4 with
          | none => pure none
          | some value => some <$> parseInt32 "read composite pg_attribute" value
        let collationSchema ← cell? "read composite pg_attribute" row 5
        let collationName ← cell? "read composite pg_attribute" row 6
        let collation ← match collationSchema, collationName with
          | none, none => pure none
          | some schema, some name => pure (some { schema, name })
          | _, _ => throw (.catalog
              "read composite pg_attribute: incomplete collation identity")
        pure (typeOid, {
          name, ordinal
          ty := ← typeRefByOid types "read composite pg_attribute" fieldTypeOid typmod
          collation
        })
      match parsed with
      | .error error => return .error error
      | .ok (typeOid, field) =>
        let some ty := typeByOid? types typeOid
          | return .error (.catalog s!"composite field refers to missing type OID {typeOid}")
        if schemas.contains ty.key.schema then
          let some index := composites.findIdx? (fun value => value.key == ty.key)
            | return .error (.catalog s!"composite field refers to non-composite {ty.key}")
          let value := composites[index]!
          composites := composites.set! index { value with fields := value.fields.push field }
    pure (.ok composites)

private def routineCatalogSql : String :=
  "SELECT p.oid::text, ns.nspname, p.proname, p.prokind::text, " ++
  "p.proretset::text, p.prorettype::text, p.pronargs::text, " ++
  "p.pronargdefaults::text, p.proisstrict::text, p.provolatile::text, " ++
  "p.proparallel::text, p.prosecdef::text, " ++
  "(EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
  "WHERE dep.classid = 'pg_catalog.pg_proc'::pg_catalog.regclass " ++
  "AND dep.objid = p.oid " ++
  "AND dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass " ++
  "AND dep.deptype = 'e'))::text " ++
  "FROM pg_catalog.pg_proc AS p " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = p.pronamespace " ++
  "ORDER BY p.oid"

private def routineArgCatalogSql : String :=
  "SELECT p.oid::text, args.ordinality::text, " ++
  "NULLIF(p.proargnames[args.ordinality], ''), " ++
  "COALESCE(p.proargmodes[args.ordinality], 'i')::text, args.type_oid::text " ++
  "FROM pg_catalog.pg_proc AS p " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(" ++
  "COALESCE(p.proallargtypes, p.proargtypes::oid[])) " ++
  "WITH ORDINALITY AS args(type_oid, ordinality) " ++
  "ORDER BY p.oid, args.ordinality"

private def isRoutineOutput : Pgx.RoutineArgMode → Bool
  | .output | .inputOutput | .table => true
  | .input | .variadic => false

private def loadRoutines (conn : Pg.Connection) (schemas : Array String)
    (types : Array CatalogType) (composites : Array Pgx.CompositeIR) :
    Async (Except Error (Array CatalogRoutine)) := do
  let mut routines : Array CatalogRoutine := #[]
  match ← queryOne conn "read pg_proc" routineCatalogSql with
  | .error error => return .error error
  | .ok rows =>
    for row in rows.rows do
      let parsed : Except Error CatalogRoutine := do
        let oid ← parseUInt32 "read pg_proc" (← cell "read pg_proc" row 0)
        let schema ← cell "read pg_proc" row 1
        let name ← cell "read pg_proc" row 2
        let kind ← parseRoutineKind "read pg_proc" (← cell "read pg_proc" row 3)
        let returnsSet ← parseBool "read pg_proc" (← cell "read pg_proc" row 4)
        let returnTypeOid ← parseUInt32 "read pg_proc" (← cell "read pg_proc" row 5)
        let inputCount ← parseNat "read pg_proc" (← cell "read pg_proc" row 6)
        let defaultCount ← parseNat "read pg_proc" (← cell "read pg_proc" row 7)
        let strict ← parseBool "read pg_proc" (← cell "read pg_proc" row 8)
        let volatility ← cell "read pg_proc" row 9
        let parallel ← cell "read pg_proc" row 10
        let securityDefiner ← parseBool "read pg_proc" (← cell "read pg_proc" row 11)
        let extensionOwned ← parseBool "read pg_proc" (← cell "read pg_proc" row 12)
        pure {
          oid, returnTypeOid, inputCount, defaultCount, extensionOwned
          ir := {
            key := { schema, name }
            kind, args := #[], returnsSet
            strict, volatility, parallel, securityDefiner
          }
        }
      match parsed with
      | .error error => return .error error
      | .ok value => routines := routines.push value
  match ← queryOne conn "read pg_proc arguments" routineArgCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    for row in rows.rows do
      let parsed : Except Error (UInt32 × Nat × Pgx.RoutineArgIR) := do
        let oid ← parseUInt32 "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 0)
        let ordinal ← parseNat "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 1)
        let name ← cell? "read pg_proc arguments" row 2
        let mode ← parseRoutineArgMode "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 3)
        let typeOid ← parseUInt32 "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 4)
        pure (oid, ordinal, {
          name, mode
          ty := ← typeRefByOid types "read pg_proc arguments" typeOid
        })
      match parsed with
      | .error error => return .error error
      | .ok (oid, ordinal, arg) =>
        match routines.findIdx? (fun value => value.oid == oid) with
        | none => pure ()
        | some index =>
          let value := routines[index]!
          unless ordinal == value.ir.args.size + 1 do
            return .error (.catalog s!"routine {value.ir.key.schema}.{value.ir.key.name} \
              has non-dense argument ordinal {ordinal}")
          routines := routines.set! index {
            value with ir := { value.ir with args := value.ir.args.push arg }
          }
    for index in [0:routines.size] do
      let value := routines[index]!
      let inputArgs := value.ir.args.filter (fun arg => arg.mode.isInput)
      unless inputArgs.size == value.inputCount do
        return .error (.catalog s!"routine {value.ir.key.schema}.{value.ir.key.name} \
          reports {value.inputCount} input arguments but exposes {inputArgs.size}")
      unless value.defaultCount ≤ value.inputCount do
        return .error (.catalog s!"routine {value.ir.key.schema}.{value.ir.key.name} \
          has more defaults than input arguments")
      let firstDefault := value.inputCount - value.defaultCount
      let mut inputPosition := 0
      let mut outputPosition := 0
      let mut args : Array Pgx.RoutineArgIR := #[]
      let mut results : Array Pgx.RoutineResultColumnIR := #[]
      for arg in value.ir.args do
        let hasDefault := arg.mode.isInput && firstDefault < inputPosition + 1
        if arg.mode.isInput then inputPosition := inputPosition + 1
        let arg := { arg with hasDefault }
        args := args.push arg
        if isRoutineOutput arg.mode then
          outputPosition := outputPosition + 1
          results := results.push {
            name := arg.name.getD s!"column{outputPosition}"
            ordinal := outputPosition
            ty := arg.ty
          }
      let returnTypeResult : Except Error (Option Pgx.TypeRef) :=
        if value.ir.kind == .procedure then pure none else
          some <$> typeRefByOid types
            s!"routine {value.ir.key.schema}.{value.ir.key.name}" value.returnTypeOid
      let returnType ← match returnTypeResult with
        | .ok result => pure result
        | .error error => return .error error
      if schemas.contains value.ir.key.schema && !value.extensionOwned &&
          value.ir.returnsSet && results.isEmpty then
        match returnType with
        | some ref =>
          if ref.key.kind == .composite then
            let candidates := composites.filter (fun composite => composite.key == ref.key)
            let some composite := candidates[0]?
              | return .error (.catalog s!"set-returning routine {value.ir.key} \
                  refers to missing composite result {ref.key}")
            unless candidates.size == 1 do
              return .error (.catalog s!"set-returning routine {value.ir.key} \
                has ambiguous composite result {ref.key}")
            for field in composite.fields do
              results := results.push {
                name := field.name
                ordinal := results.size + 1
                ty := field.ty
              }
        | none => pure ()
      let dynamicRecord := match returnType with
        | some ref => ref.key.kind == .pseudo && ref.key.name == "record" && results.isEmpty
        | none => false
      let ir := {
        value.ir with
          key := { value.ir.key with inputTypes := inputArgs.map (fun arg => arg.ty) }
          args
          returnType
          resultColumns := results
          dynamicRecord
      }
      routines := routines.set! index { value with ir }
    pure (.ok routines)

private def routineKeyByOid? (routines : Array CatalogRoutine) (oid : UInt32) :
    Option Pgx.RoutineKey :=
  routines.find? (fun value => value.oid == oid) |>.map (fun value => value.ir.key)

private def rangeCatalogSql : String :=
  "SELECT r.rngtypid::text, r.rngsubtype::text, r.rngmultitypid::text, " ++
  "cns.nspname, coll.collname, opns.nspname, opc.opcname, " ++
  "NULLIF(r.rngcanonical, 0)::text, NULLIF(r.rngsubdiff, 0)::text " ++
  "FROM pg_catalog.pg_range AS r " ++
  "LEFT JOIN pg_catalog.pg_collation AS coll ON coll.oid = NULLIF(r.rngcollation, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS cns ON cns.oid = coll.collnamespace " ++
  "JOIN pg_catalog.pg_opclass AS opc ON opc.oid = r.rngsubopc " ++
  "JOIN pg_catalog.pg_namespace AS opns ON opns.oid = opc.opcnamespace " ++
  "ORDER BY r.rngtypid"

private def loadRanges (conn : Pg.Connection) (schemas : Array String)
    (types : Array CatalogType) (routines : Array CatalogRoutine) :
    Async (Except Error (Array Pgx.RangeIR × Array Pgx.MultirangeIR)) := do
  match ← queryOne conn "read pg_range" rangeCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut ranges : Array Pgx.RangeIR := #[]
    let mut multiranges : Array Pgx.MultirangeIR := #[]
    for row in rows.rows do
      let parsed : Except Error (CatalogType × CatalogType × CatalogType ×
          Option Pgx.CollationKey × Pgx.QualifiedName × Option UInt32 × Option UInt32) := do
        let rangeOid ← parseUInt32 "read pg_range" (← cell "read pg_range" row 0)
        let subtypeOid ← parseUInt32 "read pg_range" (← cell "read pg_range" row 1)
        let multirangeOid ← parseUInt32 "read pg_range" (← cell "read pg_range" row 2)
        let some rangeType := typeByOid? types rangeOid
          | throw (.catalog s!"pg_range refers to missing range OID {rangeOid}")
        let some subtype := typeByOid? types subtypeOid
          | throw (.catalog s!"pg_range refers to missing subtype OID {subtypeOid}")
        let some multirange := typeByOid? types multirangeOid
          | throw (.catalog s!"pg_range refers to missing multirange OID {multirangeOid}")
        let collationSchema ← cell? "read pg_range" row 3
        let collationName ← cell? "read pg_range" row 4
        let collation ← match collationSchema, collationName with
          | none, none => pure none
          | some schema, some name => pure (some { schema, name })
          | _, _ => throw (.catalog "read pg_range: incomplete collation identity")
        let opclass := {
          schema := ← cell "read pg_range" row 5
          name := ← cell "read pg_range" row 6
        }
        let canonical ← match ← cell? "read pg_range" row 7 with
          | none => pure none
          | some value => some <$> parseUInt32 "read pg_range" value
        let subtypeDiff ← match ← cell? "read pg_range" row 8 with
          | none => pure none
          | some value => some <$> parseUInt32 "read pg_range" value
        pure (rangeType, subtype, multirange, collation, opclass, canonical, subtypeDiff)
      match parsed with
      | .error error => return .error error
      | .ok (rangeType, subtype, multirange, collation, opclass,
          canonicalOid, subtypeDiffOid) =>
        if schemas.contains rangeType.key.schema ||
            (Pgx.builtinTypeMapping? subtype.key).isSome then
          let canonical ← match canonicalOid with
            | none => pure none
            | some oid =>
              let some key := routineKeyByOid? routines oid
                | return .error (.catalog s!"range {rangeType.key} canonical routine OID \
                    {oid} is not visible in the configured schemas")
              pure (some key)
          let subtypeDiff ← match subtypeDiffOid with
            | none => pure none
            | some oid =>
              let some key := routineKeyByOid? routines oid
                | return .error (.catalog s!"range {rangeType.key} subtype-diff routine OID \
                    {oid} is not visible in the configured schemas")
              pure (some key)
          ranges := ranges.push {
            key := rangeType.key
            subtype := { key := subtype.key }
            multirange := multirange.key
            collation
            subtypeOpclass := opclass
            canonical
            subtypeDiff
          }
          multiranges := multiranges.push { key := multirange.key, range := rangeType.key }
    pure (.ok (ranges, multiranges))

private def loadEnums (conn : Pg.Connection) (schemas : Array String)
    (types : Array CatalogType) : Async (Except Error (Array Pgx.EnumIR)) := do
  let mut enums : Array Pgx.EnumIR := #[]
  for ty in types do
    if ty.key.kind == .enum && schemas.contains ty.key.schema then
      enums := enums.push { key := ty.key, labels := #[] }
  let sql :=
    "SELECT t.oid::text, e.enumlabel " ++
    "FROM pg_catalog.pg_type AS t " ++
    "JOIN pg_catalog.pg_enum AS e ON e.enumtypid = t.oid " ++
    "ORDER BY t.oid, e.enumsortorder"
  match ← queryOne conn "read pg_enum" sql with
  | .error error => pure (.error error)
  | .ok rows =>
    for row in rows.rows do
      let parsed : Except Error (UInt32 × String) := do
        pure (← parseUInt32 "read pg_enum" (← cell "read pg_enum" row 0),
          ← cell "read pg_enum" row 1)
      match parsed with
      | .error error => return .error error
      | .ok (oid, label) =>
        let some ty := typeByOid? types oid
          | return .error (.catalog s!"pg_enum refers to missing type OID {oid}")
        if schemas.contains ty.key.schema then
          let some index := enums.findIdx? (fun value => value.key == ty.key)
            | return .error (.catalog s!"pg_enum refers to non-enum type {ty.key}")
          let value := enums[index]!
          enums := enums.set! index { value with labels := value.labels.push label }
    pure (.ok enums)

private def loadDomains (conn : Pg.Connection) (schemas : Array String)
    (types : Array CatalogType) (enums : Array Pgx.EnumIR) :
    Async (Except Error (Array Pgx.DomainIR)) := do
  let mut domains : Array Pgx.DomainIR := #[]
  for ty in types do
    if ty.key.kind == .domain && schemas.contains ty.key.schema then
      let some base := ty.base
        | return .error (.catalog s!"domain {ty.key} has no base type")
      domains := domains.push {
        key := ty.key
        base
        notNull := ty.notNull
        defaultExpr := ty.defaultExpr
      }
  let sql :=
    "SELECT t.oid::text, c.conname, " ++
    "pg_catalog.pg_get_constraintdef(c.oid, true), c.convalidated::text, " ++
    "(EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
    "WHERE dep.classid = 'pg_catalog.pg_constraint'::pg_catalog.regclass " ++
    "AND dep.objid = c.oid " ++
    "AND dep.refclassid = 'pg_catalog.pg_proc'::pg_catalog.regclass))::text, " ++
    "(EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
    "WHERE dep.classid = 'pg_catalog.pg_constraint'::pg_catalog.regclass " ++
    "AND dep.objid = c.oid " ++
    "AND dep.refclassid = 'pg_catalog.pg_operator'::pg_catalog.regclass))::text " ++
    "FROM pg_catalog.pg_type AS t " ++
    "JOIN pg_catalog.pg_constraint AS c ON c.contypid = t.oid " ++
    "WHERE c.contype = 'c' " ++
    "ORDER BY t.oid, c.conname"
  match ← queryOne conn "read domain constraints" sql with
  | .error error => pure (.error error)
  | .ok rows =>
    for row in rows.rows do
      let parsed : Except Error (UInt32 × String × String × Bool × Bool × Bool) := do
        pure (← parseUInt32 "read domain constraints"
            (← cell "read domain constraints" row 0),
          ← cell "read domain constraints" row 1,
          ← cell "read domain constraints" row 2,
          ← parseBool "read domain constraints"
            (← cell "read domain constraints" row 3),
          ← parseBool "read domain constraints"
            (← cell "read domain constraints" row 4),
          ← parseBool "read domain constraints"
            (← cell "read domain constraints" row 5))
      match parsed with
      | .error error => return .error error
      | .ok (oid, name, definition, validated, functionDependency,
          operatorDependency) =>
        let some ty := typeByOid? types oid
          | return .error (.catalog s!"domain constraint refers to missing type OID {oid}")
        if schemas.contains ty.key.schema then
          let some index := domains.findIdx? (fun value => value.key == ty.key)
            | return .error (.catalog s!"constraint refers to non-domain type {ty.key}")
          let value := domains[index]!
          match validateLocalConstraintDependencies ty.key.display name definition
              functionDependency operatorDependency with
          | .error error => return .error error
          | .ok () => pure ()
          let parsedDefinition ← match
              ConstraintParser.parseDomainCheck value enums domains definition with
            | .ok parsed => pure parsed
            | .error diagnostic =>
                return .error (.unsupportedConstraint ty.key.display name definition diagnostic)
          match validateConstraintValidationMetadata ty.key.display name validated
              parsedDefinition.validated with
          | .error error => return .error error
          | .ok () => pure ()
          domains := domains.set! index {
            value with
              constraints := value.constraints.push definition
              localConstraints := value.localConstraints.push {
                name
                source := definition
                expression := parsedDefinition.expression
                validated
              }
          }
    pure (.ok domains)

private def relationCatalogSql : String :=
  "SELECT c.oid::text, ns.nspname, c.relname, c.relkind::text " ++
  "FROM pg_catalog.pg_class AS c " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "WHERE c.relkind IN ('r', 'p', 'v', 'm', 'f') " ++
  "ORDER BY ns.nspname, c.relname"

private def columnCatalogSql : String :=
  "SELECT c.oid::text, a.attname, a.attnum::text, a.atttypid::text, " ++
  "CASE WHEN a.atttypmod = -1 THEN NULL ELSE a.atttypmod::text END, " ++
  "a.attnotnull::text, t.typnotnull::text, " ++
  "(a.attidentity <> '')::text, (a.attgenerated <> '')::text, " ++
  "pg_catalog.pg_get_expr(ad.adbin, ad.adrelid, true), " ++
  "cns.nspname, coll.collname " ++
  "FROM pg_catalog.pg_class AS c " ++
  "JOIN pg_catalog.pg_attribute AS a ON a.attrelid = c.oid " ++
  "JOIN pg_catalog.pg_type AS t ON t.oid = a.atttypid " ++
  "LEFT JOIN pg_catalog.pg_attrdef AS ad " ++
  "ON ad.adrelid = a.attrelid AND ad.adnum = a.attnum " ++
  "LEFT JOIN pg_catalog.pg_collation AS coll ON coll.oid = NULLIF(a.attcollation, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS cns ON cns.oid = coll.collnamespace " ++
  "WHERE c.relkind IN ('r', 'p', 'v', 'm', 'f') " ++
  "AND a.attnum > 0 AND NOT a.attisdropped " ++
  "ORDER BY c.oid, a.attnum"

private def loadRelations (conn : Pg.Connection) (schemas : Array String)
    (types : Array CatalogType) :
    Async (Except Error (Array CatalogRelation)) := do
  match ← queryOne conn "read pg_class" relationCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut relations : Array CatalogRelation := #[]
    for row in rows.rows do
      let parsed : Except Error (UInt32 × String × String × Pgx.RelationKind) := do
        pure (← parseUInt32 "read pg_class" (← cell "read pg_class" row 0),
          ← cell "read pg_class" row 1,
          ← cell "read pg_class" row 2,
          ← parseRelationKind "read pg_class" (← cell "read pg_class" row 3))
      match parsed with
      | .error error => return .error error
      | .ok (oid, schema, name, kind) =>
        if schemas.contains schema then
          relations := relations.push {
            oid
            ir := { key := { schema, name }, kind, columns := #[] }
          }
    match ← queryOne conn "read pg_attribute" columnCatalogSql with
    | .error error => pure (.error error)
    | .ok columnRows =>
      for row in columnRows.rows do
        let parsed : Except Error
            (UInt32 × UInt16 × Pgx.RelationColumnIR × Bool) := do
          let relationOid ← parseUInt32 "read pg_attribute"
            (← cell "read pg_attribute" row 0)
          let name ← cell "read pg_attribute" row 1
          let attnum ← parseUInt16 "read pg_attribute"
            (← cell "read pg_attribute" row 2)
          let typeOid ← parseUInt32 "read pg_attribute"
            (← cell "read pg_attribute" row 3)
          let typmod ← match ← cell? "read pg_attribute" row 4 with
            | none => pure none
            | some value => some <$> parseInt32 "read pg_attribute" value
          let attributeNotNull ← parseBool "read pg_attribute"
            (← cell "read pg_attribute" row 5)
          let domainNotNull ← parseBool "read pg_attribute"
            (← cell "read pg_attribute" row 6)
          let identity ← parseBool "read pg_attribute"
            (← cell "read pg_attribute" row 7)
          let generated ← parseBool "read pg_attribute"
            (← cell "read pg_attribute" row 8)
          let defaultExpr ← cell? "read pg_attribute" row 9
          let collationSchema ← cell? "read pg_attribute" row 10
          let collationName ← cell? "read pg_attribute" row 11
          let collation ← match collationSchema, collationName with
            | none, none => pure none
            | some schema, some name => pure (some { schema, name })
            | _, _ => throw (.catalog "read pg_attribute: incomplete collation identity")
          let ty ← typeRefByOid types "read pg_attribute" typeOid typmod
          pure (relationOid, attnum, {
            name
            ordinal := attnum.toNat
            ty
            nullable := !(attributeNotNull || domainNotNull)
            identity
            generated
            defaultExpr
            collation
          }, attributeNotNull)
        match parsed with
        | .error error => return .error error
        | .ok (relationOid, attnum, column, attributeNotNull) =>
          match relations.findIdx? (fun relation => relation.oid == relationOid) with
          | none => pure () -- A relation outside the configured schemas.
          | some index =>
            let relation := relations[index]!
            relations := relations.set! index {
              relation with
              ir := { relation.ir with columns := relation.ir.columns.push column }
              attnums := relation.attnums.push attnum
              attributeNotNull := relation.attributeNotNull.push attributeNotNull
            }
      pure (.ok relations)

private def viewCatalogSql : String :=
  "SELECT c.oid::text, ns.nspname, c.relname, c.relkind::text, " ++
  "pg_catalog.pg_get_viewdef(c.oid, true), " ++
  "COALESCE((SELECT option_value FROM pg_catalog.pg_options_to_table(c.reloptions) " ++
  "WHERE option_name = 'check_option'), 'none'), " ++
  "COALESCE((SELECT option_value FROM pg_catalog.pg_options_to_table(c.reloptions) " ++
  "WHERE option_name = 'security_barrier'), 'false'), " ++
  "COALESCE((SELECT option_value FROM pg_catalog.pg_options_to_table(c.reloptions) " ++
  "WHERE option_name = 'security_invoker'), 'false') " ++
  "FROM pg_catalog.pg_class AS c " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "WHERE c.relkind IN ('v', 'm') " ++
  "AND NOT EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
  "WHERE dep.classid = 'pg_catalog.pg_class'::pg_catalog.regclass " ++
  "AND dep.objid = c.oid " ++
  "AND dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass " ++
  "AND dep.deptype = 'e') " ++
  "ORDER BY ns.nspname, c.relname"

private def parseViewCheckOption (context : String) : String →
    Except Error Pgx.ViewCheckOption
  | "none" => pure .none
  | "local" => pure .local
  | "cascaded" => pure .cascaded
  | value => throw (.catalog s!"{context}: unknown view check option {value}")

private def loadViews (conn : Pg.Connection) (schemas : Array String)
    (relations : Array CatalogRelation) : Async (Except Error (Array Pgx.ViewIR)) := do
  match ← queryOne conn "read view metadata" viewCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut views : Array Pgx.ViewIR := #[]
    for row in rows.rows do
      let parsed : Except Error (String × String × String × Pgx.ViewIR) := do
        let _ ← parseUInt32 "read view metadata" (← cell "read view metadata" row 0)
        let schema ← cell "read view metadata" row 1
        let name ← cell "read view metadata" row 2
        let kind ← cell "read view metadata" row 3
        let definition ← cell "read view metadata" row 4
        let rawCheckOption ← cell "read view metadata" row 5
        let rawBarrier ← cell "read view metadata" row 6
        let rawInvoker ← cell "read view metadata" row 7
        let materialized := kind == "m"
        let checkOption ← if materialized then pure .none else
          parseViewCheckOption "read view metadata" rawCheckOption
        let securityBarrier ← if materialized then pure false else
          parseBool "read view metadata" rawBarrier
        let securityInvoker ← if materialized then pure false else
          parseBool "read view metadata" rawInvoker
        pure (schema, name, kind, {
          relation := { schema, name }
          definition
          checkOption
          securityBarrier
          securityInvoker
        })
      match parsed with
      | .error error => return .error error
      | .ok (schema, name, _, view) =>
        if schemas.contains schema then
          unless relations.any (fun value => value.ir.key == ({ schema, name } : Pgx.RelationKey)) do
            return .error (.catalog s!"view metadata refers to missing relation {schema}.{name}")
          views := views.push view
    pure (.ok views)

private def loadConstraints (conn : Pg.Connection)
    (adapter : Adapter)
    (relations : Array CatalogRelation)
    (types : Array CatalogType)
    (indexes : Array CatalogIndex)
    (enums : Array Pgx.EnumIR)
    (domains : Array Pgx.DomainIR) :
    Async (Except Error (Array Pgx.ConstraintIR)) := do
  match ← queryOne conn "read pg_constraint" adapter.constraintCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut constraints : Array CatalogConstraint := #[]
    for row in rows.rows do
      let parsed : Except Error CatalogConstraint := do
        let oid ← parseUInt32 "read pg_constraint"
          (← cell "read pg_constraint" row 0)
        let relation : Pgx.RelationKey := {
          schema := ← cell "read pg_constraint" row 1
          name := ← cell "read pg_constraint" row 2
        }
        let name ← cell "read pg_constraint" row 3
        let kind ← parseConstraintKind adapter "read pg_constraint"
          (← cell "read pg_constraint" row 4)
        let referencedSchema ← cell? "read pg_constraint" row 5
        let referencedName ← cell? "read pg_constraint" row 6
        let referencedRelation ← match referencedSchema, referencedName with
          | none, none => pure none
          | some schema, some name => pure (some { schema, name })
          | _, _ => throw (.catalog
              "read pg_constraint: incomplete referenced relation identity")
        let expression ← cell? "read pg_constraint" row 7
        let validated ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 8)
        let functionDependency ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 9)
        let operatorDependency ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 10)
        let enforced ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 11)
        let deferrable ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 12)
        let initiallyDeferred ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 13)
        if initiallyDeferred && !deferrable then
          throw (.catalog s!"constraint {relation}.{name} is initially deferred but not deferrable")
        let parentSchema ← cell? "read pg_constraint" row 14
        let parentRelationName ← cell? "read pg_constraint" row 15
        let parentName ← cell? "read pg_constraint" row 16
        let parent ← match parentSchema, parentRelationName, parentName with
          | none, none, none => pure none
          | some schema, some relationName, some name => pure (some {
              relation := { schema, name := relationName }
              name
            })
          | _, _, _ => throw (.catalog
              "read pg_constraint: incomplete parent constraint identity")
        let isLocal ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 17)
        let inheritanceCount ← parseNat "read pg_constraint"
          (← cell "read pg_constraint" row 18)
        let noInherit ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 19)
        let period ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 20)
        let indexSchema ← cell? "read pg_constraint" row 21
        let indexName ← cell? "read pg_constraint" row 22
        let supportingIndex ← match indexSchema, indexName with
          | none, none => pure none
          | some schema, some name => pure (some { schema, name })
          | _, _ => throw (.catalog
              "read pg_constraint: incomplete supporting index identity")
        let foreignKeyMatch ← match ← cell? "read pg_constraint" row 23 with
          | some value => parseForeignKeyMatch "read pg_constraint" value
          | none =>
            if kind == .foreignKey then
              throw (.catalog s!"foreign key {relation}.{name} has no match type")
            else pure .simple
        let foreignKeyOnUpdate ← match ← cell? "read pg_constraint" row 24 with
          | some value => parseForeignKeyAction "read pg_constraint" value
          | none =>
            if kind == .foreignKey then
              throw (.catalog s!"foreign key {relation}.{name} has no update action")
            else pure .noAction
        let foreignKeyOnDelete ← match ← cell? "read pg_constraint" row 25 with
          | some value => parseForeignKeyAction "read pg_constraint" value
          | none =>
            if kind == .foreignKey then
              throw (.catalog s!"foreign key {relation}.{name} has no delete action")
            else pure .noAction
        let nullsNotDistinct ← parseBool "read pg_constraint"
          (← cell "read pg_constraint" row 26)
        let localExpression ← if kind == .check then
          let some source := expression
            | throw (.catalog s!"check constraint {relation}.{name} has no definition")
          let some catalogRelation := relationByKey? relations relation
            | throw (.catalog s!"check constraint {relation}.{name} has no relation")
          validateLocalConstraintDependencies relation.display name source
            functionDependency operatorDependency
          match ConstraintParser.parseTableCheck catalogRelation.ir enums domains source with
          | .ok parsed => do
              validateConstraintValidationMetadata relation.display name validated
                parsed.validated
              pure (some parsed.expression)
          | .error diagnostic =>
              throw (.unsupportedConstraint relation.display name source diagnostic)
        else pure none
        pure { oid, ir := {
          relation, name, kind, referencedRelation, expression, localExpression
          enforced, validated, deferrable, initiallyDeferred, parent, isLocal
          inheritanceCount, noInherit, period, supportingIndex
          uniqueNullPolicy := if nullsNotDistinct then .notDistinct else .distinct
          foreignKeyMatch, foreignKeyOnUpdate, foreignKeyOnDelete
        } }
      match parsed with
      | .error error => return .error error
      | .ok value =>
        if (relationByKey? relations value.ir.relation).isSome then
          constraints := constraints.push value
    match ← queryOne conn "read constraint columns" adapter.constraintColumnSql with
    | .error error => pure (.error error)
    | .ok columnRows =>
      for row in columnRows.rows do
        let parsed : Except Error (UInt32 × Bool × Nat × String) := do
          pure (← parseUInt32 "read constraint columns"
              (← cell "read constraint columns" row 0),
            ← parseBool "read constraint columns"
              (← cell "read constraint columns" row 1),
            ← parseNat "read constraint columns"
              (← cell "read constraint columns" row 2),
            ← cell "read constraint columns" row 3)
        match parsed with
        | .error error => return .error error
        | .ok (oid, referenced, ordinal, name) =>
          match constraints.findIdx? (fun value => value.oid == oid) with
          | none => pure ()
          | some index =>
            let value := constraints[index]!
            let expected := if referenced then value.ir.referencedColumns.size + 1
              else value.ir.columns.size + 1
            let lastOrdinal := if referenced then value.referencedColumnOrdinal
              else value.localColumnOrdinal
            -- `conkey` uses zero for an expression key.  The attribute join
            -- omits those entries for exclusion constraints, while the rich
            -- index key vector below retains their exact positions.
            let ordinalValid := if !referenced && value.ir.kind == .exclusion then
                ordinal > lastOrdinal
              else
                ordinal == expected
            unless ordinalValid do
              return .error (.catalog s!"constraint {value.ir.relation}.{value.ir.name}: \
                expected column ordinal {expected}, received {ordinal}")
            let ir := if referenced then
                { value.ir with
                  referencedColumns := value.ir.referencedColumns.push name }
              else
                { value.ir with columns := value.ir.columns.push name }
            let updated := if referenced then
                { value with ir, referencedColumnOrdinal := ordinal }
              else
                { value with ir, localColumnOrdinal := ordinal }
            constraints := constraints.set! index updated
      match ← queryOne conn "read foreign-key delete-set columns"
          Adapter.constraintDeleteSetColumnSql with
      | .error error => return .error error
      | .ok deleteRows =>
        for row in deleteRows.rows do
          let parsed : Except Error (UInt32 × Nat × String) := do
            pure (← parseUInt32 "read foreign-key delete-set columns"
                (← cell "read foreign-key delete-set columns" row 0),
              ← parseNat "read foreign-key delete-set columns"
                (← cell "read foreign-key delete-set columns" row 1),
              ← cell "read foreign-key delete-set columns" row 2)
          match parsed with
          | .error error => return .error error
          | .ok (oid, ordinal, name) =>
            match constraints.findIdx? (fun value => value.oid == oid) with
            | none => pure ()
            | some index =>
              let value := constraints[index]!
              let expected := value.ir.foreignKeyDeleteSetColumns.size + 1
              unless ordinal == expected do
                return .error (.catalog s!"foreign key {value.ir.relation}.{value.ir.name}: \
                  expected delete-set column ordinal {expected}, received {ordinal}")
              constraints := constraints.set! index { value with ir := {
                value.ir with foreignKeyDeleteSetColumns :=
                  value.ir.foreignKeyDeleteSetColumns.push name
              } }
      match ← queryOne conn "read constraint operators"
          Adapter.constraintOperatorSql with
      | .error error => return .error error
      | .ok operatorRows =>
        for row in operatorRows.rows do
          let parsed : Except Error (UInt32 × String × Nat × Pgx.OperatorKey) := do
            let oid ← parseUInt32 "read constraint operators"
              (← cell "read constraint operators" row 0)
            let vector ← cell "read constraint operators" row 1
            let ordinal ← parseNat "read constraint operators"
              (← cell "read constraint operators" row 2)
            let _ ← parseUInt32 "read constraint operators"
              (← cell "read constraint operators" row 3)
            let schema ← cell "read constraint operators" row 4
            let name ← cell "read constraint operators" row 5
            let leftOid ← parseUInt32 "read constraint operators"
              (← cell "read constraint operators" row 6)
            let rightOid ← parseUInt32 "read constraint operators"
              (← cell "read constraint operators" row 7)
            let key ← operatorKeyByOperandOids types "read constraint operators"
              schema name leftOid rightOid
            pure (oid, vector, ordinal, key)
          match parsed with
          | .error error => return .error error
          | .ok (oid, vector, ordinal, key) =>
            match constraints.findIdx? (fun value => value.oid == oid) with
            | none => pure ()
            | some index =>
              let value := constraints[index]!
              let current := match vector with
                | "pf" => some value.ir.referencedToReferencingOperators
                | "pp" => some value.ir.referencedEqualityOperators
                | "ff" => some value.ir.referencingEqualityOperators
                | "exclude" => some value.exclusionOperators
                | _ => none
              let some current := current
                | return .error (.catalog s!"constraint {value.ir.relation}.{value.ir.name}: \
                    unknown operator vector {vector}")
              unless ordinal == current.size + 1 do
                return .error (.catalog s!"constraint {value.ir.relation}.{value.ir.name}: \
                  expected {vector} operator ordinal {current.size + 1}, received {ordinal}")
              let updated := match vector with
                | "pf" => { value with ir := { value.ir with
                    referencedToReferencingOperators := current.push key } }
                | "pp" => { value with ir := { value.ir with
                    referencedEqualityOperators := current.push key } }
                | "ff" => { value with ir := { value.ir with
                    referencingEqualityOperators := current.push key } }
                | "exclude" => { value with exclusionOperators := current.push key }
                | _ => value
              constraints := constraints.set! index updated
      for index in [:constraints.size] do
        let value := constraints[index]!
        let checked : Except Error Pgx.ConstraintIR := match value.ir.kind with
          | .primaryKey | .unique => do
            let some key := value.ir.supportingIndex
              | throw (.catalog s!"constraint {value.ir.relation}.{value.ir.name} has no supporting index")
            let some supporting := indexes.find? (fun index => index.key == key)
              | throw (.catalog s!"constraint {value.ir.relation}.{value.ir.name} refers to missing index {key}")
            unless supporting.ir.relation == value.ir.relation do
              throw (.catalog s!"constraint {value.ir.relation}.{value.ir.name} is backed by index {key} on {supporting.ir.relation}")
            unless supporting.ir.uniqueNullPolicy == value.ir.uniqueNullPolicy do
              throw (.catalog s!"constraint {value.ir.relation}.{value.ir.name} disagrees with index {key} on null uniqueness")
            unless supporting.ir.keyElements.size == value.ir.columns.size do
              throw (.catalog s!"constraint {value.ir.relation}.{value.ir.name} has \
                {value.ir.columns.size} columns but index {key} has \
                {supporting.ir.keyElements.size} key elements")
            pure value.ir
          | .foreignKey => do
            unless value.ir.referencedRelation.isSome do
              throw (.catalog s!"foreign key {value.ir.relation}.{value.ir.name} has no referenced relation")
            let width := value.ir.columns.size
            unless width > 0 && value.ir.referencedColumns.size == width do
              throw (.catalog s!"foreign key {value.ir.relation}.{value.ir.name} has unaligned key columns")
            unless value.ir.referencedToReferencingOperators.size == width &&
                value.ir.referencedEqualityOperators.size == width &&
                value.ir.referencingEqualityOperators.size == width do
              throw (.catalog s!"foreign key {value.ir.relation}.{value.ir.name} has unaligned equality-operator vectors")
            for name in value.ir.foreignKeyDeleteSetColumns do
              unless value.ir.columns.contains name do
                throw (.catalog s!"foreign key {value.ir.relation}.{value.ir.name} has unknown delete-set column {name}")
            let some key := value.ir.supportingIndex
              | throw (.catalog s!"foreign key {value.ir.relation}.{value.ir.name} has no referenced index")
            unless indexes.any (fun index => index.key == key) do
              throw (.catalog s!"foreign key {value.ir.relation}.{value.ir.name} refers to missing index {key}")
            pure value.ir
          | .exclusion => do
            let some key := value.ir.supportingIndex
              | throw (.catalog s!"exclusion constraint {value.ir.relation}.{value.ir.name} has no supporting index")
            let some supporting := indexes.find? (fun index => index.key == key)
              | throw (.catalog s!"exclusion constraint {value.ir.relation}.{value.ir.name} refers to missing index {key}")
            unless supporting.ir.relation == value.ir.relation do
              throw (.catalog s!"exclusion constraint {value.ir.relation}.{value.ir.name} is backed by index {key} on {supporting.ir.relation}")
            unless supporting.ir.keyElements.size == value.exclusionOperators.size do
              throw (.catalog s!"exclusion constraint {value.ir.relation}.{value.ir.name} has \
                {value.exclusionOperators.size} operators but index {key} has \
                {supporting.ir.keyElements.size} key elements")
            let mut elements : Array Pgx.ExclusionElementIR := #[]
            for ordinal in [:supporting.ir.keyElements.size] do
              elements := elements.push {
                key := supporting.ir.keyElements[ordinal]!
                operator := value.exclusionOperators[ordinal]!
              }
            pure { value.ir with exclusionElements := elements }
          | .check | .notNull => do
            if value.ir.supportingIndex.isSome then
              throw (.catalog s!"constraint {value.ir.relation}.{value.ir.name} unexpectedly has a supporting index")
            pure value.ir
        match checked with
        | .error error => return .error error
        | .ok ir => constraints := constraints.set! index { value with ir }
      let mut attributeNotNull : Array AttributeNotNull := #[]
      for relation in relations do
        for index in [:relation.ir.columns.size] do
          if relation.attributeNotNull[index]! then
            let column := relation.ir.columns[index]!
            attributeNotNull := attributeNotNull.push {
              relation := relation.ir.key
              column := column.name
            }
      match adapter.normalizeConstraints (constraints.map (·.ir)) attributeNotNull with
      | .ok result => pure (.ok result)
      | .error message => pure (.error (.catalog message))

private def indexCatalogSql : String :=
  "SELECT i.indexrelid::text, ns.nspname, c.relname, ins.nspname, ic.relname, " ++
  "i.indisunique::text, i.indisprimary::text, i.indisexclusion::text, " ++
  "i.indimmediate::text, i.indisvalid::text, i.indisready::text, " ++
  "i.indislive::text, i.indnullsnotdistinct::text, am.amname, " ++
  "pg_catalog.pg_get_expr(i.indpred, i.indrelid, true), " ++
  "pg_catalog.pg_get_expr(i.indexprs, i.indrelid, true), i.indnkeyatts::text " ++
  "FROM pg_catalog.pg_index AS i " ++
  "JOIN pg_catalog.pg_class AS c ON c.oid = i.indrelid " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "JOIN pg_catalog.pg_class AS ic ON ic.oid = i.indexrelid " ++
  "JOIN pg_catalog.pg_namespace AS ins ON ins.oid = ic.relnamespace " ++
  "JOIN pg_catalog.pg_am AS am ON am.oid = ic.relam " ++
  "ORDER BY i.indexrelid"

private def indexColumnSql : String :=
  "SELECT i.indexrelid, key.ordinality, " ++
  "(key.ordinality <= i.indnkeyatts)::text, a.attname, " ++
  "CASE WHEN key.attnum = 0 THEN " ++
  "pg_catalog.pg_get_indexdef(i.indexrelid, key.ordinality::integer, true) END, " ++
  "cns.nspname, coll.collname, ons.nspname, opc.opcname, " ++
  "((COALESCE(opt.value, 0) & 1) <> 0)::text, " ++
  "((COALESCE(opt.value, 0) & 2) <> 0)::text, " ++
  "eq.operator_schema, eq.operator_name, eq.left_type::text, eq.right_type::text " ++
  "FROM pg_catalog.pg_index AS i " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(i.indkey) " ++
  "WITH ORDINALITY AS key(attnum, ordinality) " ++
  "LEFT JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = i.indrelid AND a.attnum = key.attnum " ++
  "LEFT JOIN LATERAL pg_catalog.unnest(i.indcollation) " ++
  "WITH ORDINALITY AS coll_item(oid, ordinality) " ++
  "ON coll_item.ordinality = key.ordinality " ++
  "LEFT JOIN pg_catalog.pg_collation AS coll ON coll.oid = coll_item.oid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS cns ON cns.oid = coll.collnamespace " ++
  "LEFT JOIN LATERAL pg_catalog.unnest(i.indclass) " ++
  "WITH ORDINALITY AS opclass(oid, ordinality) " ++
  "ON opclass.ordinality = key.ordinality " ++
  "LEFT JOIN pg_catalog.pg_opclass AS opc ON opc.oid = opclass.oid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS ons ON ons.oid = opc.opcnamespace " ++
  "LEFT JOIN LATERAL pg_catalog.unnest(i.indoption) " ++
  "WITH ORDINALITY AS opt(value, ordinality) " ++
  "ON opt.ordinality = key.ordinality " ++
  "LEFT JOIN pg_catalog.pg_class AS ic ON ic.oid = i.indexrelid " ++
  "LEFT JOIN pg_catalog.pg_am AS iam ON iam.oid = ic.relam " ++
  "LEFT JOIN LATERAL (" ++
  "SELECT eqns.nspname AS operator_schema, eqop.oprname AS operator_name, " ++
  "eqop.oprleft AS left_type, eqop.oprright AS right_type " ++
  "FROM pg_catalog.pg_amop AS eqamop " ++
  "JOIN pg_catalog.pg_operator AS eqop ON eqop.oid = eqamop.amopopr " ++
  "JOIN pg_catalog.pg_namespace AS eqns ON eqns.oid = eqop.oprnamespace " ++
  "WHERE eqamop.amopfamily = opc.opcfamily " ++
  "AND eqamop.amoplefttype = opc.opcintype " ++
  "AND eqamop.amoprighttype = opc.opcintype " ++
  "AND eqamop.amoppurpose = 's' " ++
  "AND ((iam.amname = 'btree' AND eqamop.amopstrategy = 3) " ++
  "OR (iam.amname = 'hash' AND eqamop.amopstrategy = 1)) " ++
  "ORDER BY eqop.oid LIMIT 1) AS eq ON true " ++
  "ORDER BY i.indexrelid, key.ordinality"

private def loadIndexes (conn : Pg.Connection)
    (relations : Array CatalogRelation) (types : Array CatalogType) :
    Async (Except Error (Array CatalogIndex)) := do
  match ← queryOne conn "read pg_index" indexCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut indexes : Array CatalogIndex := #[]
    for row in rows.rows do
      let parsed : Except Error CatalogIndex := do
        let oid ← parseUInt32 "read pg_index" (← cell "read pg_index" row 0)
        let relation : Pgx.RelationKey := {
          schema := ← cell "read pg_index" row 1
          name := ← cell "read pg_index" row 2
        }
        let key : Pgx.IndexKey := {
          schema := ← cell "read pg_index" row 3
          name := ← cell "read pg_index" row 4
        }
        let nullsNotDistinct ← parseBool "read pg_index" (← cell "read pg_index" row 12)
        pure { oid, key, ir := {
          relation
          name := key.name
          unique := ← parseBool "read pg_index" (← cell "read pg_index" row 5)
          primary := ← parseBool "read pg_index" (← cell "read pg_index" row 6)
          exclusion := ← parseBool "read pg_index" (← cell "read pg_index" row 7)
          immediate := ← parseBool "read pg_index" (← cell "read pg_index" row 8)
          valid := ← parseBool "read pg_index" (← cell "read pg_index" row 9)
          ready := ← parseBool "read pg_index" (← cell "read pg_index" row 10)
          live := ← parseBool "read pg_index" (← cell "read pg_index" row 11)
          uniqueNullPolicy := if nullsNotDistinct then .notDistinct else .distinct
          accessMethod := some (← cell "read pg_index" row 13)
          predicate := ← cell? "read pg_index" row 14
          expression := ← cell? "read pg_index" row 15
        } }
      match parsed with
      | .error error => return .error error
      | .ok value =>
        if (relationByKey? relations value.ir.relation).isSome then
          indexes := indexes.push value
    match ← queryOne conn "read index columns" indexColumnSql with
    | .error error => pure (.error error)
    | .ok columnRows =>
      for row in columnRows.rows do
        let parsed : Except Error
            (UInt32 × Bool × Option String × Option String × Option Pgx.CollationKey ×
              Option Pgx.QualifiedName × Pgx.IndexOrder × Pgx.IndexNullsOrder ×
              Option Pgx.OperatorKey) := do
          let oid ← parseUInt32 "read index columns" (← cell "read index columns" row 0)
          let keyElement ← parseBool "read index columns" (← cell "read index columns" row 2)
          let name ← cell? "read index columns" row 3
          let expression ← cell? "read index columns" row 4
          let collationSchema ← cell? "read index columns" row 5
          let collationName ← cell? "read index columns" row 6
          let collation ← match collationSchema, collationName with
            | none, none => pure none
            | some schema, some name => pure (some { schema, name })
            | _, _ => throw (.catalog "read index columns: incomplete collation identity")
          let opclassSchema ← cell? "read index columns" row 7
          let opclassName ← cell? "read index columns" row 8
          let opclass ← match opclassSchema, opclassName with
            | none, none => pure none
            | some schema, some name => pure (some { schema, name })
            | _, _ => throw (.catalog "read index columns: incomplete operator-class identity")
          let descending ← parseBool "read index columns" (← cell "read index columns" row 9)
          let nullsFirst ← parseBool "read index columns" (← cell "read index columns" row 10)
          let operatorSchema ← cell? "read index columns" row 11
          let operatorName ← cell? "read index columns" row 12
          let leftOid ← (← cell? "read index columns" row 13).mapM
            (parseUInt32 "read index equality operator")
          let rightOid ← (← cell? "read index columns" row 14).mapM
            (parseUInt32 "read index equality operator")
          let equalityOperator ← match operatorSchema, operatorName, leftOid, rightOid with
            | none, none, none, none => pure none
            | some schema, some name, some leftOid, some rightOid =>
                some <$> operatorKeyByOperandOids types "read index equality operator"
                  schema name leftOid rightOid
            | _, _, _, _ => throw (.catalog
                "read index columns: incomplete equality-operator identity")
          pure (oid, keyElement, name, expression, collation, opclass,
            if descending then .descending else .ascending,
            if nullsFirst then .first else .last, equalityOperator)
        match parsed with
        | .error error => return .error error
        | .ok (oid, keyElement, name, expression, collation, opclass,
            order, nullsOrder, equalityOperator) =>
          match indexes.findIdx? (fun value => value.oid == oid) with
          | none => pure ()
          | some index =>
            let value := indexes[index]!
            if keyElement then
              unless name.isSome != expression.isSome do
                return .error (.catalog
                  s!"index {value.key.display} key must be exactly one column or expression")
              let element : Pgx.IndexKeyElementIR := {
                ordinal := value.ir.keyElements.size + 1
                column := name
                expression
                collation
                opclass
                equalityOperator
                order
                nullsOrder
              }
              indexes := indexes.set! index { value with ir := {
                value.ir with
                columns := match name with
                  | some name => value.ir.columns.push name
                  | none => value.ir.columns
                keyElements := value.ir.keyElements.push element
              } }
            else
              let some name := name
                | return .error (.catalog
                    s!"index {value.key.display} INCLUDE element is not a column")
              if expression.isSome then
                return .error (.catalog
                  s!"index {value.key.display} INCLUDE column has an expression")
              indexes := indexes.set! index { value with ir := {
                value.ir with includedColumns := value.ir.includedColumns.push name
              } }
      pure (.ok indexes)

private def loadExtensions (conn : Pg.Connection) (required : Array String) :
    Async (Except Error (Array (String × String))) := do
  let sql :=
    "SELECT extname, extversion FROM pg_catalog.pg_extension ORDER BY extname"
  match ← queryOne conn "read pg_extension" sql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut installed : Array (String × String) := #[]
    for row in rows.rows do
      let parsed : Except Error (String × String) := do
        pure (← cell "read pg_extension" row 0, ← cell "read pg_extension" row 1)
      match parsed with
      | .error error => return .error error
      | .ok value => installed := installed.push value
    let mut result : Array (String × String) := #[]
    for name in required do
      let some value := installed.find? (fun value => value.1 == name)
        | return .error (.catalog s!"required extension {name} is not installed")
      result := result.push value
    pure (.ok result)

private partial def ensureTypeSupported (config : Config) (snapshot : CatalogSnapshot)
    (context : String) (key : Pgx.TypeKey) (seen : Array Pgx.TypeKey := #[]) :
    Except Error Unit := do
  if config.typeOverrides.any (fun value => value.key == key) then
    return
  if (Pgx.builtinTypeMapping? key).isSome then
    return
  if snapshot.enums.any (fun value => value.key == key) then
    return
  if seen.contains key then
    throw (.catalog s!"{context}: cyclic generated type dependency at {key}")
  match snapshot.domains.find? (fun value => value.key == key) with
  | some domain =>
    ensureTypeSupported config snapshot context domain.base.key (seen.push key)
  | none =>
    match snapshot.arrays.find? (fun value => value.key == key) with
    | some array =>
      unless array.delimiter == "," do
        throw (.unsupportedType
          s!"{context}: array delimiter {repr array.delimiter} is unsupported" key)
      ensureTypeSupported config snapshot context array.element.key (seen.push key)
    | none =>
      match snapshot.composites.find? (fun value => value.key == key) with
      | some composite =>
        for field in composite.fields do
          ensureTypeSupported config snapshot
            s!"{context}, composite field {composite.key}.{field.name}"
            field.ty.key (seen.push key)
      | none =>
        match snapshot.ranges.find? (fun value => value.key == key) with
        | some range =>
          ensureTypeSupported config snapshot context range.subtype.key (seen.push key)
        | none =>
          match snapshot.multiranges.find? (fun value => value.key == key) with
          | some multirange =>
            ensureTypeSupported config snapshot context multirange.range (seen.push key)
          | none => throw (.unsupportedType context key)

private def validateCatalogTypes (config : Config) (snapshot : CatalogSnapshot) :
    Except Error Unit := do
  for domain in snapshot.domains do
    ensureTypeSupported config snapshot s!"domain {domain.key}" domain.base.key
  for array in snapshot.arrays do
    if config.schemas.contains array.key.schema then
      ensureTypeSupported config snapshot s!"array {array.key}" array.key
  for composite in snapshot.composites do
    ensureTypeSupported config snapshot s!"composite {composite.key}" composite.key
  for range in snapshot.ranges do
    if config.schemas.contains range.key.schema then
      ensureTypeSupported config snapshot s!"range {range.key}" range.key
  for multirange in snapshot.multiranges do
    if config.schemas.contains multirange.key.schema then
      ensureTypeSupported config snapshot s!"multirange {multirange.key}" multirange.key
  for relation in snapshot.relations do
    for column in relation.ir.columns do
      ensureTypeSupported config snapshot
        s!"column {relation.ir.key}.{column.name}" column.ty.key

private def closeStatement (conn : Pg.Connection) (name : String) :
    Async (Except Error Unit) := do
  match ← conn.run #[.closeStatement name, .sync] with
  | .error error => pure (.error (.postgres s!"close prepared statement {name}" error))
  | .ok events =>
    for event in events do
      match event with
      | .errorResponse fields =>
        return .error (.postgres s!"close prepared statement {name}" (.server fields))
      | _ => pure ()
    pure (.ok ())

private def explainSql (statement : Pg.Statement) : String :=
  let params := String.intercalate ", "
    (List.replicate statement.paramTypes.size "NULL")
  let invocation := if statement.paramTypes.isEmpty then ""
    else "(" ++ params ++ ")"
  "EXPLAIN (VERBOSE, FORMAT JSON) EXECUTE " ++
    sqlIdentifier statement.name ++ invocation

private def knownPlanNodeTypes : Array String := #[
  "Aggregate", "Append", "BitmapAnd", "Bitmap Heap Scan", "Bitmap Index Scan",
  "BitmapOr", "CTE Scan", "Custom Scan", "Delete", "Foreign Scan",
  "Function Scan", "Gather", "Gather Merge", "Group", "Hash", "Hash Join",
  "Incremental Sort", "Index Only Scan", "Index Scan", "Insert", "Limit",
  "LockRows", "Materialize", "Memoize", "Merge", "Merge Append", "Merge Join",
  "ModifyTable", "Named Tuplestore Scan", "Nested Loop", "ProjectSet",
  "Recursive Union", "Result", "Sample Scan", "Seq Scan", "SetOp", "Sort",
  "Subquery Scan", "Table Function Scan", "Tid Range Scan", "Tid Scan",
  "Unique", "Update", "Values Scan", "WindowAgg", "WorkTable Scan"
]

private def combineAnalysis (left right : OuterJoinAnalysis) : OuterJoinAnalysis :=
  match left, right with
  | .outerJoin, _ | _, .outerJoin => .outerJoin
  | .uncertain, _ | _, .uncertain => .uncertain
  | .noOuterJoin, .noOuterJoin => .noOuterJoin

private def classifyJoinType : Option Lean.Json → OuterJoinAnalysis
  | none => .noOuterJoin
  | some (.str kind) =>
    if kind.startsWith "Left" || kind.startsWith "Right" || kind.startsWith "Full" then
      .outerJoin
    else if kind == "Inner" || kind == "Semi" || kind == "Anti" then
      .noOuterJoin
    else
      .uncertain
  | some _ => .uncertain

private def relationScanNodeTypes : Array String := #[
  "Bitmap Heap Scan", "Foreign Scan", "Index Only Scan", "Index Scan",
  "Sample Scan", "Seq Scan", "Tid Range Scan", "Tid Scan"
]

private def planRelation? (fields : Std.TreeMap.Raw String Lean.Json) (kind : String) :
    Option Pgx.RelationKey := do
  guard (relationScanNodeTypes.contains kind)
  let .str schema ← fields.get? "Schema" | none
  let .str name ← fields.get? "Relation Name" | none
  some { schema, name }

private partial def analyzePlanNode : Lean.Json →
    OuterJoinAnalysis × Array Pgx.RelationKey
  | .obj fields =>
    let join := classifyJoinType (fields.get? "Join Type")
    if join == .outerJoin then
      (.outerJoin, #[])
    else
      let kind := match fields.get? "Node Type" with
        | some (.str kind) => some kind
        | _ => none
      let shape := match kind with
        | some kind =>
          if knownPlanNodeTypes.contains kind then .noOuterJoin else .uncertain
        | _ => .uncertain
      let ownRelations := match kind with
        | some kind => (planRelation? fields kind).map (fun key => #[key]) |>.getD #[]
        | none => #[]
      let children : OuterJoinAnalysis × Array Pgx.RelationKey :=
        match fields.get? "Plans" with
        | none => (.noOuterJoin, #[])
        | some (.arr plans) => plans.foldl
            (fun result plan =>
              let child := analyzePlanNode plan
              (combineAnalysis result.1 child.1, result.2 ++ child.2))
            (.noOuterJoin, #[])
        | some _ => (.uncertain, #[])
      (combineAnalysis join (combineAnalysis shape children.1),
        ownRelations ++ children.2)
  | _ => (.uncertain, #[])

private def preservedRelations (analysis : OuterJoinAnalysis)
    (scans : Array Pgx.RelationKey) : Array Pgx.RelationKey :=
  if analysis != .noOuterJoin then #[]
  else scans.filter fun key => (scans.filter (fun found => found == key)).size == 1

/-- Pure conservative classifier for the nullability and same-row facts used
by local refinement propagation. -/
def analyzeQueryPlanJson (json : String) : QueryPlanAnalysis :=
  match Lean.Json.parse json with
  | .error _ => { outerJoins := .uncertain }
  | .ok (.arr plans) =>
    if plans.size != 1 then { outerJoins := .uncertain }
    else match plans[0]! with
      | .obj root => match root.get? "Plan" with
        | some plan =>
          let (outerJoins, scans) := analyzePlanNode plan
          { outerJoins, rowPreservedRelations := preservedRelations outerJoins scans }
        | none => { outerJoins := .uncertain }
      | _ => { outerJoins := .uncertain }
  | .ok _ => { outerJoins := .uncertain }

/-- Pure classifier for PostgreSQL's `EXPLAIN (VERBOSE, FORMAT JSON)` output.
Malformed JSON, an unknown node/join kind, or an unexpected root shape is
uncertain and therefore cannot justify a non-optional generated field. -/
def analyzeOuterJoinPlanJson (json : String) : OuterJoinAnalysis :=
  (analyzeQueryPlanJson json).outerJoins

private def inspectExplainRows (rows : Pg.Rows) : QueryPlanAnalysis :=
  if rows.rows.size != 1 || rows.columns.size != 1 then
    { outerJoins := .uncertain }
  else match rows.rows[0]? with
    | none => { outerJoins := .uncertain }
    | some row => match row[0]? with
      | none | some none => { outerJoins := .uncertain }
      | some (some bytes) => match String.fromUTF8? bytes with
        | none => { outerJoins := .uncertain }
        | some json => analyzeQueryPlanJson json

/-- Inspect a prepared statement under a forced generic plan.  A server-side
EXPLAIN failure or an unrecognized JSON shape is deliberately reported as
`uncertain`; failure to restore a setting changed by this function is a hard
probe error. -/
def analyzeQueryPlan (conn : Pg.Connection) (statement : Pg.Statement) :
    Async (Except Error QueryPlanAnalysis) := do
  let previous ← match ← currentSetting conn "plan_cache_mode" with
    | .ok value => pure value
    | .error _ => return .ok { outerJoins := .uncertain }
  match ← setConfig conn "plan_cache_mode" "force_generic_plan" with
  | .error _ => return .ok { outerJoins := .uncertain }
  | .ok () => pure ()
  let analysis ← match ← queryOne conn
      s!"inspect query plan for {statement.name}" (explainSql statement) with
    | .ok rows => pure (inspectExplainRows rows)
    | .error _ => pure { outerJoins := .uncertain }
  match ← setConfig conn "plan_cache_mode" previous with
  | .error error => pure (.error error)
  | .ok () => pure (.ok analysis)

private def orderedParameters (query : QueryInput) : Array ParameterInput :=
  query.parameters.toList.mergeSort
    (fun left right => left.position < right.position) |>.toArray

private def queryHash (sql : String) : String :=
  Pg.Crypto.toHexLower (Pg.Crypto.sha256 sql.toUTF8)

private def statementName (query : QueryInput) : String :=
  "_lean_pgx_probe_" ++ (queryHash (query.name ++ "\x00" ++ query.sql)).take 32

private def analyzePrepared (conn : Pg.Connection) (config : Config)
    (snapshot : CatalogSnapshot) (query : QueryInput) (statement : Pg.Statement) :
    Async (Except Error Pgx.QueryIR) := do
  let metadata := orderedParameters query
  unless metadata.size == statement.paramTypes.size do
    return .error (.invalidQuery query.name
      s!"manifest declares {metadata.size} parameters but PostgreSQL inferred \
        {statement.paramTypes.size}")
  let mut params : Array Pgx.ParamIR := #[]
  for index in [:statement.paramTypes.size] do
    let input := metadata[index]!
    let typeOid := statement.paramTypes[index]!
    let ty ← match typeRefByOid snapshot.types
        s!"parameter {input.position} of query {query.name}" typeOid with
      | .ok value => pure value
      | .error error => return .error error
    match ensureTypeSupported config snapshot
        s!"parameter {input.position} of query {query.name}" ty.key with
    | .error error => return .error error
    | .ok () => pure ()
    params := params.push {
      position := input.position
      name := input.name
      ty
      nullable := input.nullable
    }
  match query.cardinality with
  | .execute =>
    unless statement.columns.isEmpty do
      return .error (.invalidQuery query.name
        "execute cardinality cannot be used with a statement that returns columns")
  | .exactlyOne | .zeroOrOne | .many =>
    if statement.columns.isEmpty then
      return .error (.invalidQuery query.name
        "a row-returning cardinality requires at least one result column")
  let mut names : Array String := #[]
  let mut directColumns : Array Pgx.QueryColumnIR := #[]
  for column in statement.columns do
    if isBlank column.name then
      return .error (.invalidQuery query.name "result column name is empty")
    if names.contains column.name then
      return .error (.invalidQuery query.name
        s!"result column name {column.name} is duplicated")
    names := names.push column.name
    let typmod := if column.typeMod == -1 then none else some column.typeMod
    let ty ← match typeRefByOid snapshot.types
        s!"result column {column.name} of query {query.name}" column.typeOid typmod with
      | .ok value => pure value
      | .error error => return .error error
    match ensureTypeSupported config snapshot
        s!"result column {column.name} of query {query.name}" ty.key with
    | .error error => return .error error
    | .ok () => pure ()
    let originInfo := relationOrigin? snapshot.relations column.tableOid column.attnum
    let origin := originInfo.map (·.1)
    let sourceColumn := originInfo.map (·.2)
    let logicalType ← match sourceColumn with
      | none => pure none
      | some source =>
          match logicalTypeForDirectProjection snapshot.domains query.name column.name source ty with
          | .ok value => pure value
          | .error error => return .error error
    directColumns := directColumns.push {
      name := column.name
      ty
      logicalType
      nullable := sourceColumn.map (·.nullable) |>.getD true
      origin
      collation := sourceColumn.bind (·.collation)
    }
  let (columns, rowPreservedRelations) ← if directColumns.isEmpty then
      pure (directColumns, #[])
    else
      match ← analyzeQueryPlan conn statement with
      | .error error => return .error error
      | .ok analysis =>
        let preserved := analysis.rowPreservedRelations.filter fun key =>
          directColumns.any fun column =>
            column.origin.map (fun origin => origin.relation == key) |>.getD false
        match analysis.outerJoins with
        | .noOuterJoin => pure (directColumns, preserved)
        | .outerJoin | .uncertain =>
          pure (directColumns.map (fun column => {
            column with nullable := true, nullWidened := true
          }), #[])
  pure (.ok {
    name := query.name
    sql := query.sql
    sqlHash := queryHash query.sql
    params
    columns
    rowPreservedRelations
    cardinality := query.cardinality
  })

private def analyzeQuery (conn : Pg.Connection) (config : Config)
    (snapshot : CatalogSnapshot) (query : QueryInput) :
    Async (Except Error Pgx.QueryIR) := do
  let name := statementName query
  match ← Pg.Connection.prepare conn name query.sql #[] with
  | .error error => pure (.error (.postgres s!"Parse/Describe query {query.name}" error))
  | .ok statement =>
    let result ← analyzePrepared conn config snapshot query statement
    let closed ← closeStatement conn name
    match result, closed with
    | .error error, _ => pure (.error error)
    | .ok _, .error error => pure (.error error)
    | .ok query, .ok () => pure (.ok query)

private def loadSnapshot (conn : Pg.Connection) (config : Config) :
    Async (Except Error CatalogSnapshot) := do
  let serverMajor ← match ← loadServerMajor conn with
    | .error error => return .error error
    | .ok value => pure value
  unless config.supportedServerMajors.contains serverMajor do
    return .error (.catalog s!"PostgreSQL major {serverMajor} is not in the configured \
      supported set {repr config.supportedServerMajors}")
  let some adapter := adapterForServerMajor? serverMajor
    | return .error (.catalog s!"PostgreSQL major {serverMajor} has no probe adapter")
  let schemas ← match ← loadSchemas conn config.schemas with
    | .error error => return .error error
    | .ok value => pure value
  let types ← match ← loadTypes conn with
    | .error error => return .error error
    | .ok value => pure value
  let extensionTypeOwnership ← match ← loadExtensionTypeOwnership conn types with
    | .error error => return .error error
    | .ok value => pure value
  let arrays ← match loadArrays config.schemas types with
    | .error error => return .error error
    | .ok value => pure value
  let enums ← match ← loadEnums conn config.schemas types with
    | .error error => return .error error
    | .ok value => pure value
  let domains ← match ← loadDomains conn config.schemas types enums with
    | .error error => return .error error
    | .ok value => pure value
  let composites ← match ← loadComposites conn config.schemas types with
    | .error error => return .error error
    | .ok value => pure value
  let catalogRoutines ← match ← loadRoutines conn config.schemas types composites with
    | .error error => return .error error
    | .ok value => pure value
  let (ranges, multiranges) ← match
      ← loadRanges conn config.schemas types catalogRoutines with
    | .error error => return .error error
    | .ok value => pure value
  let relations ← match ← loadRelations conn config.schemas types with
    | .error error => return .error error
    | .ok value => pure value
  let views ← match ← loadViews conn config.schemas relations with
    | .error error => return .error error
    | .ok value => pure value
  let catalogIndexes ← match ← loadIndexes conn relations types with
    | .error error => return .error error
    | .ok value => pure value
  let constraints ← match
      ← loadConstraints conn adapter relations types catalogIndexes enums domains with
    | .error error => return .error error
    | .ok value => pure value
  let indexes := catalogIndexes.map (·.ir)
  let extensions ← match ← loadExtensions conn config.requiredExtensions with
    | .error error => return .error error
    | .ok value => pure value
  pure (.ok {
    serverMajor, schemas, types, enums, arrays, domains, composites, ranges,
    multiranges, relations, views
    routines := catalogRoutines.filter (fun value =>
      config.schemas.contains value.ir.key.schema && !value.extensionOwned)
      |>.map (fun value => value.ir)
    constraints, indexes, extensions, extensionTypeOwnership
  })

/-- Probe a migrated live server and return a fully symbolic, normalized
database contract. PostgreSQL's extended-protocol `Parse` is the sole SQL
statement parser, so every `QueryInput.sql` is necessarily one statement. -/
def probeDatabase (conn : Pg.Connection) (config : Config) :
    Async (Except Error Pgx.DatabaseIR) := do
  match validateConfig config with
  | .error error => return .error error
  | .ok () => pure ()
  match ← configureSession conn config.session with
  | .error error => return .error error
  | .ok () => pure ()
  let snapshot ← match ← loadSnapshot conn config with
    | .error error => return .error error
    | .ok value => pure value
  match validateLiveTypeOverrides config.typeOverrides (snapshot.types.map (·.key)) with
  | .error error => return .error error
  | .ok () => pure ()
  match validateExtensionCodecOwnership config.extensionCodecPackages
      snapshot.extensionTypeOwnership with
  | .error error => return .error error
  | .ok () => pure ()
  match validateCatalogTypes config snapshot with
  | .error error => return .error error
  | .ok () => pure ()
  let mut queries : Array Pgx.QueryIR := #[]
  for query in config.queries do
    match ← analyzeQuery conn config snapshot query with
    | .error error => return .error error
    | .ok value => queries := queries.push value
  let extensionCodecPackages ← match
      config.resolvedExtensionCodecPackages snapshot.extensions with
    | .error error => return .error error
    | .ok value => pure value
  let database : Pgx.DatabaseIR := {
    serverMajor := snapshot.serverMajor
    supportedServerMajors := config.normalizedSupportedServerMajors
    session := config.session
    schemas := snapshot.schemas
    enums := snapshot.enums
    arrays := snapshot.arrays
    domains := snapshot.domains
    composites := snapshot.composites
    ranges := snapshot.ranges
    multiranges := snapshot.multiranges
    relations := snapshot.relations.map (·.ir)
    views := snapshot.views
    routines := snapshot.routines
    constraints := snapshot.constraints
    indexes := snapshot.indexes
    queries
    requiredExtensions := snapshot.extensions
    typeOverrides := config.typeOverrides
    extensionCodecPackages
  }
  pure (.ok (Projection.planDatabase database).normalize)

end Pgx.Codegen.Probe
