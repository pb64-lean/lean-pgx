import Pgx.Codegen.Emit
import Pgx.Codegen.Manifest
import Pgx.Codegen.Probe
import Pgx.IR.Json
import Pg.Connection

/-!
# Hermetic PostgreSQL code-generation entry point

The Bazel rule owns server lifecycle and passes only declared files here.  This
program applies migrations, asks PostgreSQL to describe the literal queries,
normalizes the symbolic contract, and writes the rule's explicit outputs.
-/

namespace Pgx.Codegen.Main

open Std.Async

private structure Options where
  probeOnly : Bool := false
  url : Option String := none
  modulePrefix : Option String := none
  canonicalMajor : Option Nat := none
  manifest : Option String := none
  serverMajors : Array Nat := #[]
  schemas : Array String := #[]
  migrations : Array String := #[]
  queryNames : Array String := #[]
  queryFiles : Array String := #[]
  typesOut : Option String := none
  schemaOut : Option String := none
  constraintsOut : Option String := none
  rootOut : Option String := none
  irOut : Option String := none
  contractOut : Option String := none
  compatibilityOut : Option String := none
  queryOuts : Array (String × String) := #[]

private def duplicateOption (name : String) : Except String α :=
  throw s!"option {name} may be supplied only once"

private def setStringOption (name value : String) (current : Option String) :
    Except String (Option String) :=
  if current.isSome then duplicateOption name else pure (some value)

private def parseNatOption (name value : String) : Except String Nat := do
  let some parsed := value.toNat?
    | throw s!"option {name} expects a nonnegative integer, received {repr value}"
  pure parsed

private def splitPair (value : String) : Except String (String × String) :=
  match value.splitOn "=" with
  | [name, path] =>
      if name.isEmpty || path.isEmpty then
        throw s!"query output must be NAME=PATH, received {repr value}"
      else
        pure (name, path)
  | _ => throw s!"query output must be NAME=PATH, received {repr value}"

private def parseArgs : List String → Options → Except String Options
  | [], options => pure options
  | "--probe-only" :: rest, options =>
      if options.probeOnly then duplicateOption "--probe-only"
      else parseArgs rest { options with probeOnly := true }
  | "--url" :: value :: rest, options => do
      parseArgs rest { options with url := ← setStringOption "--url" value options.url }
  | "--module-prefix" :: value :: rest, options => do
      parseArgs rest {
        options with modulePrefix := ← setStringOption "--module-prefix" value options.modulePrefix
      }
  | "--canonical-major" :: value :: rest, options => do
      if options.canonicalMajor.isSome then duplicateOption "--canonical-major"
      parseArgs rest { options with canonicalMajor := some (← parseNatOption "--canonical-major" value) }
  | "--manifest" :: value :: rest, options => do
      parseArgs rest {
        options with manifest := ← setStringOption "--manifest" value options.manifest
      }
  | "--server-major" :: value :: rest, options => do
      let major ← parseNatOption "--server-major" value
      parseArgs rest {
        options with serverMajors := options.serverMajors.push major
      }
  | "--schema" :: value :: rest, options =>
      parseArgs rest { options with schemas := options.schemas.push value }
  | "--migration" :: value :: rest, options =>
      parseArgs rest { options with migrations := options.migrations.push value }
  | "--query-name" :: value :: rest, options =>
      parseArgs rest { options with queryNames := options.queryNames.push value }
  | "--query-file" :: value :: rest, options =>
      parseArgs rest { options with queryFiles := options.queryFiles.push value }
  | "--types-out" :: value :: rest, options => do
      parseArgs rest {
        options with typesOut := ← setStringOption "--types-out" value options.typesOut
      }
  | "--schema-out" :: value :: rest, options => do
      parseArgs rest {
        options with schemaOut := ← setStringOption "--schema-out" value options.schemaOut
      }
  | "--constraints-out" :: value :: rest, options => do
      let output ← setStringOption "--constraints-out" value options.constraintsOut
      parseArgs rest {
        options with constraintsOut := output
      }
  | "--root-out" :: value :: rest, options => do
      parseArgs rest {
        options with rootOut := ← setStringOption "--root-out" value options.rootOut
      }
  | "--ir-out" :: value :: rest, options => do
      parseArgs rest { options with irOut := ← setStringOption "--ir-out" value options.irOut }
  | "--contract-out" :: value :: rest, options => do
      parseArgs rest {
        options with contractOut := ← setStringOption "--contract-out" value options.contractOut
      }
  | "--compatibility-out" :: value :: rest, options => do
      let output ← setStringOption "--compatibility-out" value options.compatibilityOut
      parseArgs rest {
        options with compatibilityOut := output
      }
  | "--query-out" :: value :: rest, options => do
      parseArgs rest { options with queryOuts := options.queryOuts.push (← splitPair value) }
  | option :: _, _ => throw s!"unknown or incomplete code-generation option {repr option}"

private def required (name : String) : Option α → Except String α
  | some value => pure value
  | none => throw s!"missing required option {name}"

private def hasDuplicates [BEq α] (values : Array α) : Bool := Id.run do
  let mut seen : Array α := #[]
  for value in values do
    if seen.contains value then return true
    seen := seen.push value
  return false

private def sortedNats (values : Array Nat) : Array Nat :=
  values.toList.mergeSort (· < ·) |>.toArray

private def validateOptions (options : Options) : Except String Unit := do
  let _ ← required "--url" options.url
  let _ ← required "--module-prefix" options.modulePrefix
  let canonicalMajor ← required "--canonical-major" options.canonicalMajor
  if canonicalMajor == 0 then throw "--canonical-major must be positive"
  let _ ← required "--manifest" options.manifest
  let _ ← required "--ir-out" options.irOut
  let _ ← required "--contract-out" options.contractOut
  let _ ← required "--compatibility-out" options.compatibilityOut
  if options.serverMajors.isEmpty then throw "at least one --server-major is required"
  if hasDuplicates options.serverMajors then throw "--server-major values contain duplicates"
  unless options.serverMajors.contains canonicalMajor do
    throw "--canonical-major must occur in the supported --server-major set"
  if options.schemas.isEmpty then throw "at least one --schema is required"
  if hasDuplicates options.schemas then throw "--schema values contain duplicates"
  unless options.queryNames.size == options.queryFiles.size do
    throw s!"received {options.queryNames.size} query names but {options.queryFiles.size} query files"
  if hasDuplicates options.queryNames then throw "--query-name values contain duplicates"
  if hasDuplicates options.queryFiles then throw "--query-file values contain duplicates"
  if options.probeOnly then
    unless options.queryOuts.isEmpty do
      throw "--query-out is not accepted with --probe-only"
  else
    let _ ← required "--types-out" options.typesOut
    let _ ← required "--schema-out" options.schemaOut
    let _ ← required "--constraints-out" options.constraintsOut
    let _ ← required "--root-out" options.rootOut
    unless options.queryOuts.size == options.queryFiles.size do
      throw s!"received {options.queryOuts.size} query outputs for {options.queryFiles.size} queries"
    if hasDuplicates (options.queryOuts.map (·.1)) then
      throw "--query-out names contain duplicates"
    if hasDuplicates (options.queryOuts.map (·.2)) then
      throw "--query-out paths contain duplicates"
    for name in options.queryNames do
      unless (options.queryOuts.map (·.1)).contains name do
        throw s!"query {name} has no declared --query-out"

private structure LoadedInput where
  manifest : Pgx.Codegen.Manifest
  queries : Array Probe.QueryInput

private def loadInputs (options : Options) : IO (Except String LoadedInput) := do
  let manifestPath ← match required "--manifest" options.manifest with
    | .ok value => pure value
    | .error error => return .error error
  let document ← IO.FS.readFile manifestPath
  let manifest ← match Pgx.Codegen.Manifest.parse document with
    | .ok value => pure value
    | .error error => return .error s!"manifest {manifestPath}: {error}"
  match Pgx.Codegen.Manifest.validateQueryFiles manifest options.queryFiles with
  | .error error => return .error error
  | .ok () => pure ()
  let buildMajors := sortedNats options.serverMajors
  unless manifest.supportedServerMajors == buildMajors do
    return .error s!"manifest supportedServerMajors {repr manifest.supportedServerMajors} does not match build rule {repr buildMajors}"
  let mut queries : Array Probe.QueryInput := #[]
  for index in [0:options.queryFiles.size] do
    let path := options.queryFiles[index]!
    let declaredName := options.queryNames[index]!
    let some entry := Pgx.Codegen.Manifest.queryForFile? manifest path
      | return .error s!"query file {path} has no manifest entry"
    unless entry.leanName == declaredName do
      return .error s!"query file {path} declares Lean name {entry.leanName}, but Bazel declared {declaredName}"
    let sql ← IO.FS.readFile path
    queries := queries.push {
      name := entry.leanName
      sql
      cardinality := entry.cardinality
      parameters := entry.parameters.map fun parameter => {
        position := parameter.position
        name := parameter.name
        nullable := parameter.nullable
      }
    }
  pure (.ok { manifest, queries })

private def execSql (conn : Pg.Connection) (context sql : String) :
    Async (Except String Unit) := do
  match ← Pg.Connection.exec conn sql with
  | .ok _ => pure (.ok ())
  | .error error => pure (.error s!"{context}: {error}")

private def replayMigrations (conn : Pg.Connection) (paths : Array String) :
    Async (Except String Unit) := do
  for path in paths do
    let sql ← IO.FS.readFile path
    match ← execSql conn s!"migration {path}" sql with
    | .ok () => pure ()
    | .error error => return .error error
  pure (.ok ())

private def probe (options : Options) (loaded : LoadedInput) :
    Async (Except String Pgx.DatabaseIR) := do
  let url ← match required "--url" options.url with
    | .ok value => pure value
    | .error error => return .error error
  let config ← match Pg.ConnectConfig.parseUri url with
    | .ok value => pure value
    | .error error => return .error s!"invalid PostgreSQL URL: {error}"
  let conn ← Pg.connect config
  let result ← match ← replayMigrations conn options.migrations with
    | .error error => pure (.error error)
    | .ok () =>
      let probeConfig : Probe.Config := {
        schemas := options.schemas
        session := { searchPath := options.schemas }
        queries := loaded.queries
        supportedServerMajors := options.serverMajors
        requiredExtensions := loaded.manifest.requiredExtensionNames
        typeOverrides := loaded.manifest.resolvedTypeOverrides
      }
      match ← Probe.probeDatabase conn probeConfig with
      | .ok database => pure (.ok database)
      | .error error => pure (.error (toString error))
  Pg.Connection.close conn
  pure result

private def writeText (path contents : String) : IO Unit := do
  let file := System.FilePath.mk path
  match file.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  IO.FS.writeFile file contents

private def writeOutputs (options : Options) (database : Pgx.DatabaseIR)
    (sources : GeneratedSources) : IO (Except String Unit) := do
  let modulePrefix ← match required "--module-prefix" options.modulePrefix with
    | .ok value => pure value
    | .error error => return .error error
  unless sources.modulePrefix == modulePrefix do
    return .error s!"module prefix {repr modulePrefix} normalizes to {repr sources.modulePrefix}; use the normalized spelling in the Bazel target"
  let typesOut ← match required "--types-out" options.typesOut with
    | .ok value => pure value
    | .error error => return .error error
  let schemaOut ← match required "--schema-out" options.schemaOut with
    | .ok value => pure value
    | .error error => return .error error
  let constraintsOut ← match required "--constraints-out" options.constraintsOut with
    | .ok value => pure value
    | .error error => return .error error
  let rootOut ← match required "--root-out" options.rootOut with
    | .ok value => pure value
    | .error error => return .error error
  let irOut ← match required "--ir-out" options.irOut with
    | .ok value => pure value
    | .error error => return .error error
  let compatibilityOut ← match required "--compatibility-out" options.compatibilityOut with
    | .ok value => pure value
    | .error error => return .error error
  let contractOut ← match required "--contract-out" options.contractOut with
    | .ok value => pure value
    | .error error => return .error error
  writeText typesOut sources.types.contents
  writeText schemaOut sources.schema.contents
  writeText constraintsOut sources.constraints.contents
  writeText rootOut sources.root.contents
  for (name, path) in options.queryOuts do
    let suffix := ".Queries." ++ name
    let some source := sources.queries.find? (fun source => source.moduleName.endsWith suffix)
      | return .error s!"emitter produced no query module for declared output {name}"
    writeText path source.contents
  writeText irOut database.renderSnapshot
  writeText contractOut (database.contractHash ++ "\n")
  writeText compatibilityOut (database.compatibilityHash ++ "\n")
  pure (.ok ())

private def writeProbeOutputs (options : Options) (database : Pgx.DatabaseIR) :
    IO (Except String Unit) := do
  let irOut ← match required "--ir-out" options.irOut with
    | .ok value => pure value
    | .error error => return .error error
  let compatibilityOut ← match required "--compatibility-out" options.compatibilityOut with
    | .ok value => pure value
    | .error error => return .error error
  let contractOut ← match required "--contract-out" options.contractOut with
    | .ok value => pure value
    | .error error => return .error error
  writeText irOut database.renderSnapshot
  writeText contractOut (database.contractHash ++ "\n")
  writeText compatibilityOut (database.compatibilityHash ++ "\n")
  pure (.ok ())

private def generate (args : List String) : Async (Except String Unit) := do
  let options ← match parseArgs args {} with
    | .ok value => pure value
    | .error error => return .error error
  match validateOptions options with
  | .error error => return .error error
  | .ok () => pure ()
  let loaded ← match ← loadInputs options with
    | .ok value => pure value
    | .error error => return .error error
  let database ← match ← probe options loaded with
    | .ok value => pure value
    | .error error => return .error error
  let canonicalMajor ← match required "--canonical-major" options.canonicalMajor with
    | .ok value => pure value
    | .error error => return .error error
  unless database.serverMajor == canonicalMajor do
    return .error s!"connected PostgreSQL major {database.serverMajor}, expected canonical major {canonicalMajor}"
  if options.probeOnly then
    return ← writeProbeOutputs options database
  let modulePrefix ← match required "--module-prefix" options.modulePrefix with
    | .ok value => pure value
    | .error error => return .error error
  let sources ← match emitDatabase modulePrefix database with
    | .ok value => pure value
    | .error error => return .error (toString error)
  writeOutputs options database sources

def main (args : List String) : IO UInt32 :=
  Async.block do
    try
      match ← generate args with
      | .ok () => pure 0
      | .error error =>
          IO.eprintln s!"lean-pgx code generation failed: {error}"
          pure 1
    catch error =>
      IO.eprintln s!"lean-pgx code generation failed: {error}"
      pure 1

end Pgx.Codegen.Main

def main (args : List String) : IO UInt32 := Pgx.Codegen.Main.main args
