import Pgx.IR.Json
import Lean.Data.Json

/-!
# Typed-query manifest

The manifest follows the query-object shape from `discussion.md`: every query
is keyed by the basename of its literal `.sql` file.  Two reserved root keys,
`supportedServerMajors` and `typeOverrides`, carry optional generation-wide
configuration.
-/

namespace Pgx.Codegen

open Lean

/-- A named positional parameter supplied by the manifest.  PostgreSQL fills
in its SQL type later, when the literal statement is described. -/
structure ManifestParameter where
  position : Nat
  name : String
  nullable : Bool
  deriving Repr, BEq, Inhabited

/-- Manifest facts associated with one SQL source basename. -/
structure ManifestQuery where
  sqlBasename : String
  leanName : String
  cardinality : Cardinality
  parameters : Array ManifestParameter
  deriving Repr, BEq, Inhabited

/-- Fully validated contents of a query manifest. -/
structure Manifest where
  queries : Array ManifestQuery
  supportedServerMajors : Array Nat := #[17, 18]
  typeOverrides : Array TypeOverrideIR := #[]
  deriving Repr, BEq, Inhabited

namespace Manifest

private def requiredField [FromJson α]
    (json : Json) (field : String) : Except String α := do
  let value ← match json.getObjVal? field with
    | .ok value => pure value
    | .error error => throw s!"field '{field}': {error}"
  match fromJson? value with
  | .ok result => pure result
  | .error error => throw s!"field '{field}': {error}"

private def optionalField [FromJson α]
    (json : Json) (field : String) (default : α) : Except String α := do
  let object ← json.getObj?
  match object.get? field with
  | none => pure default
  | some value =>
      match fromJson? value with
      | .ok result => pure result
      | .error error => throw s!"field '{field}': {error}"

private def sqlBasenameFromPath (path : String) : String :=
  let slashName := (path.splitOn "/").getLast?.getD path
  (slashName.splitOn "\\").getLast?.getD slashName

private def hasPathSeparator (value : String) : Bool :=
  value.toList.any fun char => char == '/' || char == '\\'

private def capitalizeWords (chars : List Char) : List Char :=
  let rec loop (capitalize : Bool) : List Char → List Char
    | [] => []
    | char :: rest =>
        if char.isAlphanum then
          (if capitalize then char.toUpper else char) :: loop false rest
        else
          loop true rest
  loop true chars

/-- Deterministically derive the generated Lean module name for a SQL
basename.  Non-alphanumeric separators delimit words, so `get_user.sql`
becomes `GetUser`. -/
def expectedLeanName (sqlBasename : String) : Except String String := do
  if sqlBasename.isEmpty then
    throw "SQL basename must not be empty"
  if hasPathSeparator sqlBasename then
    throw s!"query key '{sqlBasename}' must be a file basename, not a path"
  if !sqlBasename.endsWith ".sql" then
    throw s!"query key '{sqlBasename}' must end in '.sql'"
  let stem := (sqlBasename.dropEnd 4).toString
  let result := String.ofList (capitalizeWords stem.toList)
  if result.isEmpty then
    throw s!"query key '{sqlBasename}' does not contain a Lean name"
  match result.toList with
  | first :: _ =>
      if first.isAlpha then
        pure result
      else
        throw s!"query key '{sqlBasename}' derives invalid Lean name '{result}'"
  | [] => throw s!"query key '{sqlBasename}' does not contain a Lean name"

private def parseParameter (json : Json) : Except String ManifestParameter := do
  pure {
    position := ← requiredField json "position"
    name := ← requiredField json "name"
    nullable := ← requiredField json "nullable"
  }

private def parseParameters (json : Json) : Except String (Array ManifestParameter) := do
  let values ← json.getArr?
  values.mapM parseParameter

private def sortParameters
    (parameters : Array ManifestParameter) : Array ManifestParameter :=
  parameters.toList.mergeSort (fun left right => left.position < right.position)
    |>.toArray

private def validateDensePositions
    (sqlBasename : String) (parameters : Array ManifestParameter) : Except String Unit :=
  let rec loop (expected : Nat) : List ManifestParameter → Except String Unit
    | [] => pure ()
    | parameter :: rest => do
        if parameter.position == expected then
          loop (expected + 1) rest
        else
          throw s!"query '{sqlBasename}' parameters must have dense positions 1 through n; \
            expected {expected}, found {parameter.position}"
  loop 1 parameters.toList

private def firstDuplicate? (values : Array String) : Option String :=
  let rec loop (seen : List String) : List String → Option String
    | [] => none
    | value :: rest =>
        if seen.contains value then some value else loop (value :: seen) rest
  loop [] values.toList

private def validateParameterNames
    (sqlBasename : String) (parameters : Array ManifestParameter) : Except String Unit := do
  for parameter in parameters do
    if parameter.name.isEmpty || parameter.name.trimAscii.toString != parameter.name then
      throw s!"query '{sqlBasename}' parameter {parameter.position} has an empty or untrimmed name"
  match firstDuplicate? (parameters.map (fun parameter => parameter.name)) with
  | some duplicate =>
      throw s!"query '{sqlBasename}' has duplicate parameter name '{duplicate}'"
  | none => pure ()

private def parseCardinality
    (sqlBasename : String) (json : Json) : Except String Cardinality :=
  match (fromJson? json : Except String Cardinality) with
  | .ok cardinality => pure cardinality
  | .error _ =>
      throw s!"query '{sqlBasename}' cardinality must be one of \
        'execute', 'exactlyOne', 'zeroOrOne', or 'many'"

private def parseQuery
    (sqlBasename : String) (json : Json) : Except String ManifestQuery := do
  let expected ← expectedLeanName sqlBasename
  let leanName : String ← requiredField json "leanName"
  if leanName.isEmpty || leanName.trimAscii.toString != leanName then
    throw s!"query '{sqlBasename}' has an empty or untrimmed leanName"
  if leanName != expected then
    throw s!"query '{sqlBasename}' leanName must be '{expected}', found '{leanName}'"
  let cardinalityJson ← match json.getObjVal? "cardinality" with
    | .ok value => pure value
    | .error error => throw s!"query '{sqlBasename}' field 'cardinality': {error}"
  let cardinality ← parseCardinality sqlBasename cardinalityJson
  let parameterJson ← match json.getObjVal? "parameters" with
    | .ok value => pure value
    | .error error => throw s!"query '{sqlBasename}' field 'parameters': {error}"
  let parameters ← parseParameters parameterJson
  let parameters := sortParameters parameters
  validateDensePositions sqlBasename parameters
  validateParameterNames sqlBasename parameters
  pure { sqlBasename, leanName, cardinality, parameters }

private def sortQueries (queries : Array ManifestQuery) : Array ManifestQuery :=
  queries.toList.mergeSort (fun left right => left.sqlBasename < right.sqlBasename)
    |>.toArray

private def sortMajors (majors : Array Nat) : Array Nat :=
  majors.toList.mergeSort (fun left right => left < right) |>.toArray

private def validateMajors (majors : Array Nat) : Except String (Array Nat) := do
  if majors.isEmpty then
    throw "supportedServerMajors must not be empty"
  if majors.any (fun major => major == 0) then
    throw "supportedServerMajors entries must be positive"
  match firstDuplicate? (majors.map toString) with
  | some duplicate => throw s!"duplicate supported server major '{duplicate}'"
  | none => pure (sortMajors majors)

private def validateTypeOverrides
    (overrides : Array TypeOverrideIR) : Except String Unit := do
  for override in overrides do
    if override.key.schema.isEmpty || override.key.name.isEmpty then
      throw "type override schema and name must not be empty"
    if override.leanType.isEmpty || override.leanType.trimAscii.toString != override.leanType then
      throw s!"type override for '{override.key}' has an empty or untrimmed leanType"
    if override.codec.isEmpty || override.codec.trimAscii.toString != override.codec then
      throw s!"type override for '{override.key}' has an empty or untrimmed codec"
    match override.importModule with
    | none => pure ()
    | some moduleName =>
        if moduleName.isEmpty || moduleName.trimAscii.toString != moduleName then
          throw s!"type override for '{override.key}' has an empty or untrimmed importModule"
  for index in [0 : overrides.size] do
    for otherIndex in [index + 1 : overrides.size] do
      if overrides[index]!.key == overrides[otherIndex]!.key then
        throw s!"duplicate type override for '{overrides[index]!.key}'"

private def sortTypeOverrides
    (overrides : Array TypeOverrideIR) : Array TypeOverrideIR :=
  overrides.toList.mergeSort (fun left right =>
    let leftKey := s!"{left.key.schema}\u0000{left.key.name}\u0000{left.key.kind.tag}"
    let rightKey := s!"{right.key.schema}\u0000{right.key.name}\u0000{right.key.kind.tag}"
    leftKey < rightKey) |>.toArray

/-- Decode and validate a manifest JSON value. -/
def fromJson (json : Json) : Except String Manifest := do
  let object ← json.getObj?
  let configuredMajors : Array Nat ←
    optionalField json "supportedServerMajors" #[17, 18]
  let supportedServerMajors ← validateMajors configuredMajors
  let typeOverrides : Array TypeOverrideIR ← optionalField json "typeOverrides" #[]
  validateTypeOverrides typeOverrides
  let mut queries := #[]
  for (sqlBasename, value) in object.toList do
    if sqlBasename != "supportedServerMajors" && sqlBasename != "typeOverrides" then
      let query ← parseQuery sqlBasename value
      queries := queries.push query
  let sortedQueries := sortQueries queries
  match firstDuplicate? (sortedQueries.map (fun query => query.leanName)) with
  | some duplicate => throw s!"duplicate query leanName '{duplicate}'"
  | none => pure ()
  pure {
    queries := sortedQueries
    supportedServerMajors
    typeOverrides := sortTypeOverrides typeOverrides
  }

/-- Parse and validate a manifest document. -/
def parse (document : String) : Except String Manifest := do
  let json ← Json.parse document
  fromJson json

/-- Find a manifest entry using exactly the SQL basename stored at the root. -/
def queryForBasename? (manifest : Manifest) (sqlBasename : String) :
    Option ManifestQuery :=
  manifest.queries.find? fun query => query.sqlBasename == sqlBasename

/-- Find a manifest entry for a declared SQL source path.  Only its basename is
part of the manifest contract. -/
def queryForFile? (manifest : Manifest) (sqlFile : String) : Option ManifestQuery :=
  queryForBasename? manifest (sqlBasenameFromPath sqlFile)

/-- Check that manifest entries and declared query source files have an exact
one-to-one basename association. -/
def validateQueryFiles
    (manifest : Manifest) (sqlFiles : Array String) : Except String Unit := do
  let basenames := sqlFiles.map sqlBasenameFromPath
  match firstDuplicate? basenames with
  | some duplicate => throw s!"query sources have duplicate basename '{duplicate}'"
  | none => pure ()
  for basename in basenames do
    let _ ← expectedLeanName basename
    if (queryForBasename? manifest basename).isNone then
      throw s!"query source '{basename}' has no manifest entry"
  for query in manifest.queries do
    if !basenames.contains query.sqlBasename then
      throw s!"manifest entry '{query.sqlBasename}' has no declared query source"

end Manifest

end Pgx.Codegen
