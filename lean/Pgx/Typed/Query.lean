module

public import Pgx.Typed.Catalog

public section

/-!
# Checked prepared-query execution

Every path verifies Parse/Describe metadata before binding and verifies the
portal RowDescription again before any generated decoder sees bytes.
-/

namespace Pgx.Typed

open Std.Async

private def queryKey (db : DatabaseDesc)
    (spec : QuerySpec db Params Row cardinality) : String :=
  if spec.cacheKey.isEmpty then
    queryCacheKey db.contractHash spec.contractHash spec.sql
  else
    spec.cacheKey

private def statementName (key : String) : String :=
  "pgx_" ++ String.ofList (key.toList.take 48)

private def executionFailure (error : Pg.Error) : Error :=
  match error with
  | .server fields =>
    if fields.sqlState? == some "0A000" &&
        (fields.message?.map (·.contains "cached plan")).getD false then
      .queryDrift (fields.message?.getD "cached plan changed its result type")
    else
      .postgres error
  | _ => .postgres error

private def acceptCachedPlan (key : String) (spec : QuerySpec db Params Row cardinality)
    (plan : PreparedQueryPlan db) : Except Error (PreparedQueryPlan db) := do
  verifyPreparedQueryIdentity plan key spec.contractHash spec.params.size
    spec.columns.size spec.resultFormats.size
  pure plan

private def prepareChecked (db : DatabaseDesc)
    (spec : QuerySpec db Params Row cardinality) (conn : CheckedConnection db) :
    Async (Except Error (PreparedQueryPlan db)) := do
  let key := queryKey db spec
  match ← Internal.beginPrepare conn key with
  | .ready plan => pure (acceptCachedPlan key spec plan)
  | .failed error => pure (.error error)
  | .wait completion => do
    let result ← await completion
    pure <| result.bind (acceptCachedPlan key spec)
  | .owner =>
    match resolvePreparedParams conn.catalog spec.params with
    | .error error =>
      let result := Except.error error
      Internal.completePrepare conn key result
      pure result
    | .ok resolvedParams =>
      let paramOids := resolvedParams.map (fun value => value.oid)
      match ← Pg.Connection.prepare conn.raw (statementName key) spec.sql paramOids with
      | .error error =>
        let result := Except.error (Internal.preparationFailure error)
        Internal.completePrepare conn key result
        pure result
      | .ok statement =>
        let result := createPreparedQueryPlan conn.catalog key spec.contractHash spec.params
          resolvedParams spec.columns spec.resultFormats statement
        -- Parse/Describe succeeded, so any subsequent descriptor-plan failure
        -- must remain sticky: retrying this named statement would collide with
        -- the one PostgreSQL has already installed on this session.
        Internal.completePrepare conn key result true
        pure result

private def validateEncodedParams (expected : Nat) (encoded : @& EncodedParams) :
    Except Error Unit := do
  unless encoded.values.size == expected do
    throw (.encode
      s!"generated encoder returned {encoded.values.size} values for {expected} parameters")
  unless encoded.formats.size == expected do
    throw (.encode
      s!"generated encoder returned {encoded.formats.size} formats for {expected} parameters")
  match encoded.formats.find? (fun format => !(format == 0 || format == 1)) with
  | some format =>
    throw (.encode s!"unsupported PostgreSQL parameter format {format}")
  | none => pure ()

namespace ParameterValidationBenchmark

/-- Exact production validation seam for the focused differential benchmark. -/
@[noinline] def validateCandidate (expected : Nat) (encoded : @& EncodedParams) :
    Except Error Unit :=
  validateEncodedParams expected encoded

end ParameterValidationBenchmark

private def runChecked (db : DatabaseDesc)
    (spec : QuerySpec db Params Row cardinality) (conn : CheckedConnection db)
    (params : Params) : Async (Except Error (PreparedQueryPlan db × Pg.SpanRows)) := do
  let plan ← match ← prepareChecked db spec conn with
    | .error error => return .error error
    | .ok plan => pure plan
  let encodedResult := match spec.preparedEncode with
    | some encode => encode plan.resolve plan.params params
    | none => spec.encode conn.catalog params
  -- Keep these synchronous admission branches nested: lifting either success
  -- into `Async` would allocate and bind an already-resolved task.
  match encodedResult with
  | .error error => pure (.error error)
  | .ok encoded =>
    match validateEncodedParams spec.params.size encoded with
    | .error error => pure (.error error)
    | .ok () => do
      let rows ← match ← Pg.Connection.executeSpans conn.raw plan.statement.name
          encoded.values encoded.formats plan.resultFormats with
        | .error error =>
          let failure := executionFailure error
          Internal.markPreparedDrift conn plan.cacheKey failure
          return .error failure
        | .ok rows => pure rows
      match verifyPreparedResultColumns plan rows.columns with
      | .error error =>
        Internal.markPreparedDrift conn plan.cacheKey error
        pure (.error error)
      | .ok () => pure (.ok (plan, rows))

private def decodeRow (spec : QuerySpec db Params Row cardinality)
    (plan : PreparedQueryPlan db)
    (catalog : ResolvedCatalog db) (columns : Array Pg.Protocol.ColumnDesc)
    (values : Pg.Protocol.DataRowSpans) : Except Error Row := do
  unless values.size == spec.columns.size do
    throw (.queryDrift
      s!"data row has {values.size} fields; expected {spec.columns.size}")
  match spec.preparedSpanDecode with
  | some decode => decode plan.resolve plan.results columns values
  | none =>
    let materialized := values.materialize
    match spec.preparedDecode with
    | some decode => decode plan.resolve plan.results columns materialized
    | none => spec.decode catalog columns materialized

/-- Execute a checked command that has no result columns. -/
def execute (spec : QuerySpec db Params Row .execute)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error CommandResult) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok (_, rows) =>
    if rows.rows.isEmpty then pure (.ok { tag := rows.tag })
    else pure (.error (.queryDrift
      s!"execute query unexpectedly returned {rows.rows.size} data rows"))

/-- Execute a checked query whose application contract requires one row. -/
def fetchOne (spec : QuerySpec db Params Row .exactlyOne)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error Row) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok (plan, rows) =>
    match rows.rows with
    | #[values] => pure (decodeRow spec plan conn.catalog rows.columns values)
    | values => pure (.error (.cardinality "exactly one row" s!"{values.size} rows"))

/-- Execute a checked query whose application contract permits at most one
row. -/
def fetchOptional (spec : QuerySpec db Params Row .zeroOrOne)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error (Option Row)) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok (plan, rows) =>
    match rows.rows with
    | #[] => pure (.ok none)
    | #[values] => pure (some <$> decodeRow spec plan conn.catalog rows.columns values)
    | values => pure (.error (.cardinality "zero or one row" s!"{values.size} rows"))

/-- Execute a checked query returning all buffered rows in server order. -/
def fetchMany (spec : QuerySpec db Params Row .many)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error (Array Row)) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok (plan, rows) =>
    pure (rows.rows.mapM (decodeRow spec plan conn.catalog rows.columns))

end Pgx.Typed
