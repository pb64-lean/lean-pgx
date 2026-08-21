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
    (values : Pg.Protocol.DataRowSpans) : Except Error Row :=
  if values.size = spec.columns.size then
    match spec.preparedSpanDecoderBundle with
    | some bundle => bundle.row plan.resolve plan.results columns values
    | none =>
      match spec.preparedSpanDecode with
      | some decode => decode plan.resolve plan.results columns values
      | none =>
        let materialized := values.materialize
        match spec.preparedDecode with
        | some decode => decode plan.resolve plan.results columns materialized
        | none => spec.decode catalog columns materialized
  else
    throw (dataRowArityError values.size spec.columns.size)

private def decodeManyRowsReference (spec : QuerySpec db Params Row .many)
    (plan : PreparedQueryPlan db) (catalog : ResolvedCatalog db)
    (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  rows.mapM (decodeRow spec plan catalog columns)

/-- Keep legacy decoder projections outside the generated-bundle fast path.
This helper is deliberately not inlined: a specification with a matching
bundle must not retain callbacks that cannot be selected. -/
@[noinline] private def decodeManyRowsWithoutBundle
    (expectedColumns : Nat) (spec : QuerySpec db Params Row .many)
    (plan : PreparedQueryPlan db) (catalog : ResolvedCatalog db)
    (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  match spec.preparedSpanDecode with
  | some decode =>
    guardedPreparedSpanRows expectedColumns decode
      plan.resolve plan.results columns rows
  | none =>
    match spec.preparedDecode with
    | some decode =>
      rows.mapM fun values =>
        if values.size = expectedColumns then
          let materialized := values.materialize
          decode plan.resolve plan.results columns materialized
        else
          throw (dataRowArityError values.size expectedColumns)
    | none =>
      let decode := spec.decode
      rows.mapM fun values =>
        if values.size = expectedColumns then
          let materialized := values.materialize
          decode catalog columns materialized
        else
          throw (dataRowArityError values.size expectedColumns)

/-- Keep the compatible row callback outside the matching-bundle fast path.
The specification width, rather than the mismatched bundle width, continues
to guard every row before the callback runs. -/
@[noinline] private def decodeManyRowsBundleWidthMismatch
    (expectedColumns : Nat) (bundle : PreparedSpanDecoderBundle Row)
    (plan : PreparedQueryPlan db) (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  guardedPreparedSpanRows expectedColumns bundle.row
    plan.resolve plan.results columns rows

/-- Select the generated prepared decoder once for a complete result batch.
The row-arity guard deliberately remains inside each specialized map so a
malformed row has the same error and left-to-right precedence as `decodeRow`.
The fallback branches retain the same per-row materialization behavior.  The
staged helpers also keep unused legacy and row callbacks out of the matching
generated-bundle ownership path. -/
private def decodeManyRowsCandidate (spec : QuerySpec db Params Row .many)
    (plan : PreparedQueryPlan db) (catalog : ResolvedCatalog db)
    (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  let expectedColumns := spec.columns.size
  match spec.preparedSpanDecoderBundle with
  | some bundle =>
    if bundle.expectedColumns = expectedColumns then
      bundle.many plan.resolve plan.results columns rows
    else
      decodeManyRowsBundleWidthMismatch expectedColumns bundle plan columns rows
  | none =>
    decodeManyRowsWithoutBundle expectedColumns spec plan catalog columns rows

private theorem decodeManyRowsCandidate_eq_reference
    (spec : QuerySpec db Params Row .many) (plan : PreparedQueryPlan db)
    (catalog : ResolvedCatalog db) (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) :
    decodeManyRowsCandidate spec plan catalog columns rows =
      decodeManyRowsReference spec plan catalog columns rows := by
  cases bundleCase : spec.preparedSpanDecoderBundle with
  | some bundle =>
    by_cases expectedCase : bundle.expectedColumns = spec.columns.size
    · simp only [decodeManyRowsCandidate, bundleCase, expectedCase, ↓reduceIte]
      rw [bundle.many_eq_guardedRow, expectedCase]
      unfold guardedPreparedSpanRows decodeManyRowsReference
      apply congrArg (fun decode => rows.mapM decode)
      funext values
      simp [decodeRow, bundleCase]
    · simp only [decodeManyRowsCandidate, bundleCase, expectedCase, ↓reduceIte]
      unfold decodeManyRowsBundleWidthMismatch
      unfold guardedPreparedSpanRows decodeManyRowsReference
      apply congrArg (fun decode => rows.mapM decode)
      funext values
      simp [decodeRow, bundleCase]
  | none =>
    simp only [decodeManyRowsCandidate, decodeManyRowsReference, bundleCase]
    unfold decodeManyRowsWithoutBundle
    split <;> rename_i spanCase
    · unfold guardedPreparedSpanRows
      apply congrArg (fun decode => rows.mapM decode)
      funext values
      simp [decodeRow, bundleCase, spanCase]
    · split <;> rename_i preparedCase
      · apply congrArg (fun decode => rows.mapM decode)
        funext values
        simp [decodeRow, bundleCase, spanCase, preparedCase]
      · apply congrArg (fun decode => rows.mapM decode)
        funext values
        simp [decodeRow, bundleCase, spanCase, preparedCase]

namespace PreparedRowDispatchBenchmark

/-- Exact former per-row decoder dispatch for semantic and counter checks. -/
@[noinline] def decodeReference (spec : QuerySpec db Params Row .many)
    (plan : PreparedQueryPlan db) (catalog : ResolvedCatalog db)
    (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  decodeManyRowsReference spec plan catalog columns rows

/-- Exact selected-once production candidate for semantic and counter checks. -/
@[noinline] def decodeCandidate (spec : QuerySpec db Params Row .many)
    (plan : PreparedQueryPlan db) (catalog : ResolvedCatalog db)
    (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  decodeManyRowsCandidate spec plan catalog columns rows

/-- Hoisting decoder selection preserves every result and first error. -/
theorem decodeCandidate_eq_decodeReference
    (spec : QuerySpec db Params Row .many) (plan : PreparedQueryPlan db)
    (catalog : ResolvedCatalog db) (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) :
    decodeCandidate spec plan catalog columns rows =
      decodeReference spec plan catalog columns rows := by
  exact decodeManyRowsCandidate_eq_reference spec plan catalog columns rows

end PreparedRowDispatchBenchmark

/-- Logical production keeps the former per-row dispatch; compiled production
uses the proved selected-once batch dispatcher. -/
@[implemented_by decodeManyRowsCandidate]
private def decodeManyRows (spec : QuerySpec db Params Row .many)
    (plan : PreparedQueryPlan db) (catalog : ResolvedCatalog db)
    (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  decodeManyRowsReference spec plan catalog columns rows

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
    pure (decodeManyRows spec plan conn.catalog rows.columns rows.rows)

end Pgx.Typed
