import Pgx.Test.PreparedRowDispatchEager

/-!
Focused semantic test and differential benchmark for prepared row-decoder
dispatch.  The reference performs callback selection for every row, the eager
candidate preserves PGX-13's exact selected-once dispatcher, and the candidate
is the staged dispatcher used by compiled `fetchMany`.  The `single` mode calls
the exact staged decoder used by compiled `fetchOne` and `fetchOptional`, while
the reference selector preserves the former eager single-row dispatcher.

The semantic corpus exercises the span, materialized-prepared, and generic
callbacks, including priority, exact malformed-row diagnostics, first-error
ordering, and a span value that escapes the decoder.  Each repeated hot-loop
iteration contains only row dispatch/decoding and result consumption.  Process
counters also include fixed fixture construction, semantic preflight, checksum
verification, and output; query execution and I/O are absent.
-/

namespace Pgx.Typed.PreparedRowDispatchBenchmarkHarness

open PreparedRowDispatchBenchmark
open PreparedRowDispatchBenchmarkEager

private def fixtureTypeKey : Pgx.TypeKey :=
  { schema := "pg_catalog", name := "text", kind := .base }

private def fixtureType : Pgx.TypeRef :=
  { key := fixtureTypeKey, typmod := some (-1) }

private def database : DatabaseDesc := {
  canonicalMajor := 18
  serverMajors := #[18]
  session := { searchPath := #["pg_catalog"] }
  types := #[]
  relations := #[]
  schemaHash := "prepared-row-dispatch-schema"
  contractHash := "prepared-row-dispatch-database"
}

private def catalogResult : Except Error (ResolvedCatalog database) :=
  ResolvedCatalog.create database #[] #[]

private def expectedColumns : Array ColumnSpec := #[
  { name := "left", ty := fixtureType, nullable := true },
  { name := "right", ty := fixtureType, nullable := true }
]

private def actualColumns : Array Pg.Protocol.ColumnDesc := #[
  {
    name := "left"
    tableOid := 0
    attnum := 0
    typeOid := Pg.Oid.text
    typeSize := -1
    typeMod := -1
    format := 0
  },
  {
    name := "right"
    tableOid := 0
    attnum := 0
    typeOid := Pg.Oid.text
    typeSize := -1
    typeMod := -1
    format := 0
  }
]

private def plan : PreparedQueryPlan database := {
  cacheKey := "prepared-row-dispatch-cache"
  contractHash := "prepared-row-dispatch-query"
  statement := {
    name := "prepared_row_dispatch"
    paramTypes := #[]
    columns := actualColumns
  }
  params := #[]
  results := #[]
  resolve := fun key => throw (.unsupportedType key)
  columns := #[]
  resultFormats := #[]
}

/-- Exact pre-staging single-row dispatcher used as the semantic oracle. -/
@[noinline] private def decodeSingleEager
    (spec : QuerySpec database Unit Row cardinality)
    (catalog : ResolvedCatalog database)
    (columns : Array Pg.Protocol.ColumnDesc)
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

private structure DecodedRow where
  path : Nat
  cells : Array (Option ByteArray)
  escaped : Option Pg.Protocol.DataRowSpans := none

private def sentinel := "reject".toUTF8

private def rejectSentinel (cells : Array (Option ByteArray)) : Except Error Unit := do
  if cells[0]? == some (some sentinel) then
    throw (.decode "prepared row dispatch sentinel")

private def genericDecode (_ : ResolvedCatalog database)
    (_ : Array Pg.Protocol.ColumnDesc) (cells : Array (Option ByteArray)) :
    Except Error DecodedRow := do
  rejectSentinel cells
  pure { path := 1, cells }

private def preparedDecode (_ : TypeResolver) (_ : Array ResolvedType)
    (_ : Array Pg.Protocol.ColumnDesc) (cells : Array (Option ByteArray)) :
    Except Error DecodedRow := do
  rejectSentinel cells
  pure { path := 2, cells }

private def spanDecode (_ : TypeResolver) (_ : Array ResolvedType)
    (_ : Array Pg.Protocol.ColumnDesc) (row : Pg.Protocol.DataRowSpans) :
    Except Error DecodedRow := do
  let cells := row.materialize
  rejectSentinel cells
  pure { path := 3, cells, escaped := some row }

private inductive DecoderMode where
  | span
  | prepared
  | generic

private def specFor : DecoderMode → QuerySpec database Unit DecodedRow .many
  | .span => {
      name := "span"
      sql := "SELECT left, right"
      contractHash := "span"
      params := #[]
      columns := expectedColumns
      encode := fun _ _ => pure { values := #[], formats := #[] }
      decode := genericDecode
      preparedDecode := some preparedDecode
      preparedSpanDecode := some spanDecode
    }
  | .prepared => {
      name := "prepared"
      sql := "SELECT left, right"
      contractHash := "prepared"
      params := #[]
      columns := expectedColumns
      encode := fun _ _ => pure { values := #[], formats := #[] }
      decode := genericDecode
      preparedDecode := some preparedDecode
    }
  | .generic => {
      name := "generic"
      sql := "SELECT left, right"
      contractHash := "generic"
      params := #[]
      columns := expectedColumns
      encode := fun _ _ => pure { values := #[], formats := #[] }
      decode := genericDecode
    }

private structure RowSnapshot where
  path : Nat
  cells : Array (Option ByteArray)
  escaped : Option (Array (Option ByteArray))
  deriving Repr, BEq

private inductive ResultSnapshot where
  | ok (rows : Array RowSnapshot)
  | error (kind : ErrorKind) (message : String)
  deriving Repr, BEq

private def snapshot : Except Error (Array DecodedRow) → ResultSnapshot
  | .ok rows => .ok <| rows.map fun row => {
      path := row.path
      cells := row.cells
      escaped := row.escaped.map (·.materialize)
    }
  | .error error => .error error.kind error.toMessage

private def snapshotSingle : Except Error DecodedRow → ResultSnapshot
  | .ok row => snapshot (.ok #[row])
  | .error error => .error error.kind error.toMessage

private def expectedSuccess (path : Nat) (escapes : Bool)
    (rows : Array (Array (Option ByteArray))) : ResultSnapshot :=
  .ok <| rows.map fun cells => {
    path
    cells
    escaped := if escapes then some cells else none
  }

private def spanRows (rows : Array (Array (Option ByteArray))) :
    Array Pg.Protocol.DataRowSpans :=
  rows.map Pg.Protocol.DataRowSpans.ofCells

private structure SemanticCase where
  label : String
  mode : DecoderMode
  rows : Array (Array (Option ByteArray))
  expected : ResultSnapshot

private def successCells : Array (Array (Option ByteArray)) := #[
  #[some "alpha".toUTF8, none],
  #[some "omega".toUTF8, some (ByteArray.mk #[0, 1, 2, 255])]
]

private def semanticCases : Array SemanticCase := #[
  {
    label := "span-priority-and-escape"
    mode := .span
    rows := successCells
    expected := expectedSuccess 3 true successCells
  },
  {
    label := "prepared-priority"
    mode := .prepared
    rows := successCells
    expected := expectedSuccess 2 false successCells
  },
  {
    label := "generic-fallback"
    mode := .generic
    rows := successCells
    expected := expectedSuccess 1 false successCells
  },
  {
    label := "empty-batch"
    mode := .span
    rows := #[]
    expected := .ok #[]
  },
  {
    label := "malformed-row"
    mode := .prepared
    rows := #[#[some "short".toUTF8]]
    expected := .error .queryDrift
      "query drift: data row has 1 fields; expected 2"
  },
  {
    label := "arity-precedes-callback"
    mode := .span
    rows := #[#[some sentinel]]
    expected := .error .queryDrift
      "query drift: data row has 1 fields; expected 2"
  },
  {
    label := "earlier-callback-error-precedes-later-arity"
    mode := .generic
    rows := #[#[some sentinel, none], #[some "short".toUTF8]]
    expected := .error .decode
      "row decoding failed: prepared row dispatch sentinel"
  },
  {
    label := "earlier-arity-precedes-later-callback-error"
    mode := .prepared
    rows := #[#[some "short".toUTF8], #[some sentinel, none]]
    expected := .error .queryDrift
      "query drift: data row has 1 fields; expected 2"
  }
]

private def validateSemantics (catalog : ResolvedCatalog database) : IO Nat := do
  for fixture in semanticCases do
    let spec := specFor fixture.mode
    let reference := snapshot <|
      decodeReference spec plan catalog actualColumns (spanRows fixture.rows)
    let eager := snapshot <|
      decodeEagerCandidate spec plan catalog actualColumns (spanRows fixture.rows)
    let candidate := snapshot <|
      decodeCandidate spec plan catalog actualColumns (spanRows fixture.rows)
    unless reference == fixture.expected do
      throw (IO.userError s!"{fixture.label}: reference differs from expected: {reprStr reference}")
    unless candidate == fixture.expected do
      throw (IO.userError s!"{fixture.label}: candidate differs from expected: {reprStr candidate}")
    unless eager == fixture.expected do
      throw (IO.userError s!"{fixture.label}: eager differs from expected: {reprStr eager}")
    unless reference == eager do
      throw (IO.userError s!"{fixture.label}: reference and eager differ")
    unless reference == candidate do
      throw (IO.userError s!"{fixture.label}: reference and candidate differ")
  pure semanticCases.size

private def bundleDecode (_ : TypeResolver) (_ : Array ResolvedType)
    (columns : Array Pg.Protocol.ColumnDesc) (row : Pg.Protocol.DataRowSpans) :
    Except Error DecodedRow := do
  unless columns.size == expectedColumns.size do
    throw (.queryDrift
      s!"prepared bundle has {columns.size} columns; expected {expectedColumns.size}")
  let cells := row.materialize
  rejectSentinel cells
  pure { path := 4, cells, escaped := some row }

private def decoderBundle (bundleExpectedColumns : Nat) :
    PreparedSpanDecoderBundle DecodedRow := {
  expectedColumns := bundleExpectedColumns
  row := bundleDecode
  many := guardedPreparedSpanRows bundleExpectedColumns bundleDecode
  many_eq_guardedRow := by
    intro resolve types columns rows
    rfl
}

private def bundleSpecFor (bundleExpectedColumns : Nat) :
    QuerySpec database Unit DecodedRow .many := {
  specFor .span with
  name := s!"bundle-{bundleExpectedColumns}"
  contractHash := s!"bundle-{bundleExpectedColumns}"
  preparedSpanDecoderBundle := some (decoderBundle bundleExpectedColumns)
}

private structure BundleSemanticCase where
  label : String
  bundleExpectedColumns : Nat
  columns : Array Pg.Protocol.ColumnDesc
  rows : Array (Array (Option ByteArray))
  expected : ResultSnapshot

private def malformedRow : Array (Option ByteArray) :=
  #[some "short".toUTF8]

private def sentinelRow : Array (Option ByteArray) :=
  #[some sentinel, none]

private def bundleSemanticCases : Array BundleSemanticCase := #[
  {
    label := "bundle-priority-over-legacy-callbacks"
    bundleExpectedColumns := 2
    columns := actualColumns
    rows := successCells
    expected := expectedSuccess 4 true successCells
  },
  {
    label := "bundle-expected-columns-less-than-spec"
    bundleExpectedColumns := 1
    columns := actualColumns
    rows := successCells
    expected := expectedSuccess 4 true successCells
  },
  {
    label := "bundle-expected-columns-greater-than-spec"
    bundleExpectedColumns := 3
    columns := actualColumns
    rows := successCells
    expected := expectedSuccess 4 true successCells
  },
  {
    label := "bundle-width-row-less-than-spec"
    bundleExpectedColumns := 1
    columns := actualColumns
    rows := #[#[some "bundle-width-one".toUTF8]]
    expected := .error .queryDrift
      "query drift: data row has 1 fields; expected 2"
  },
  {
    label := "bundle-width-row-greater-than-spec"
    bundleExpectedColumns := 3
    columns := actualColumns
    rows := #[#[some "bundle-width-three".toUTF8, none, none]]
    expected := .error .queryDrift
      "query drift: data row has 3 fields; expected 2"
  },
  {
    label := "bad-columns-empty-batch"
    bundleExpectedColumns := 2
    columns := actualColumns.take 1
    rows := #[]
    expected := .ok #[]
  },
  {
    label := "bad-columns-malformed-first-row"
    bundleExpectedColumns := 2
    columns := actualColumns.take 1
    rows := #[malformedRow]
    expected := .error .queryDrift
      "query drift: data row has 1 fields; expected 2"
  },
  {
    label := "bad-columns-valid-first-row"
    bundleExpectedColumns := 2
    columns := actualColumns.take 1
    rows := #[successCells[0]!]
    expected := .error .queryDrift
      "query drift: prepared bundle has 1 columns; expected 2"
  },
  {
    label := "later-malformed-row"
    bundleExpectedColumns := 2
    columns := actualColumns
    rows := #[successCells[0]!, malformedRow]
    expected := .error .queryDrift
      "query drift: data row has 1 fields; expected 2"
  },
  {
    label := "earlier-decode-error-precedes-later-malformed-row"
    bundleExpectedColumns := 2
    columns := actualColumns
    rows := #[sentinelRow, malformedRow]
    expected := .error .decode
      "row decoding failed: prepared row dispatch sentinel"
  }
]

private def validateBundleSemantics (catalog : ResolvedCatalog database) : IO Nat := do
  for fixture in bundleSemanticCases do
    let bundle := decoderBundle fixture.bundleExpectedColumns
    let spec := bundleSpecFor fixture.bundleExpectedColumns
    let rows := spanRows fixture.rows
    let reference := snapshot <|
      decodeReference spec plan catalog fixture.columns rows
    let eager := snapshot <|
      decodeEagerCandidate spec plan catalog fixture.columns rows
    let candidate := snapshot <|
      decodeCandidate spec plan catalog fixture.columns rows
    let directMany := snapshot <|
      bundle.many plan.resolve plan.results fixture.columns rows
    let guardedRows := snapshot <|
      guardedPreparedSpanRows bundle.expectedColumns bundle.row
        plan.resolve plan.results fixture.columns rows
    unless reference == fixture.expected do
      throw (IO.userError
        s!"{fixture.label}: reference differs from expected: {reprStr reference}")
    unless candidate == fixture.expected do
      throw (IO.userError
        s!"{fixture.label}: candidate differs from expected: {reprStr candidate}")
    unless eager == fixture.expected do
      throw (IO.userError
        s!"{fixture.label}: eager differs from expected: {reprStr eager}")
    unless reference == eager do
      throw (IO.userError s!"{fixture.label}: reference and eager differ")
    unless reference == candidate do
      throw (IO.userError s!"{fixture.label}: reference and candidate differ")
    unless directMany == guardedRows do
      throw (IO.userError
        s!"{fixture.label}: bundle many and guarded row decoder differ")
  pure bundleSemanticCases.size

private def validateSingleCase (label : String)
    (spec : QuerySpec database Unit DecodedRow cardinality)
    (catalog : ResolvedCatalog database)
    (columns : Array Pg.Protocol.ColumnDesc)
    (cells : Array (Option ByteArray)) (expected : ResultSnapshot) : IO Unit := do
  let row := Pg.Protocol.DataRowSpans.ofCells cells
  let eager := snapshotSingle <| decodeSingleEager spec catalog columns row
  let reference := snapshotSingle <|
    PreparedSingleRowDispatchBenchmark.decodeReference
      spec plan catalog columns row
  let candidate := snapshotSingle <|
    PreparedSingleRowDispatchBenchmark.decodeCandidate
      spec plan catalog columns row
  let production := snapshotSingle <|
    PreparedSingleRowDispatchBenchmark.decodeProduction
      spec plan catalog columns row
  unless eager == expected do
    throw (IO.userError s!"{label}: eager differs from expected: {reprStr eager}")
  unless reference == expected do
    throw (IO.userError
      s!"{label}: reference differs from expected: {reprStr reference}")
  unless candidate == expected do
    throw (IO.userError
      s!"{label}: candidate differs from expected: {reprStr candidate}")
  unless production == expected do
    throw (IO.userError
      s!"{label}: production differs from expected: {reprStr production}")
  unless eager == reference && reference == candidate && candidate == production do
    throw (IO.userError s!"{label}: single-row selectors differ")

private def validateSingleSemantics (catalog : ResolvedCatalog database) : IO Nat := do
  let first := successCells[0]!
  validateSingleCase "single-span-priority-and-escape" (specFor .span)
    catalog actualColumns first (expectedSuccess 3 true #[first])
  validateSingleCase "single-prepared-priority" (specFor .prepared)
    catalog actualColumns first (expectedSuccess 2 false #[first])
  validateSingleCase "single-generic-fallback" (specFor .generic)
    catalog actualColumns first (expectedSuccess 1 false #[first])
  validateSingleCase "single-bundle-priority" (bundleSpecFor 2)
    catalog actualColumns first (expectedSuccess 4 true #[first])
  validateSingleCase "single-bundle-width-is-not-a-row-guard" (bundleSpecFor 1)
    catalog actualColumns first (expectedSuccess 4 true #[first])
  validateSingleCase "single-arity-precedes-callback" (specFor .span)
    catalog actualColumns malformedRow
    (.error .queryDrift "query drift: data row has 1 fields; expected 2")
  validateSingleCase "single-callback-error" (specFor .span)
    catalog actualColumns sentinelRow
    (.error .decode "row decoding failed: prepared row dispatch sentinel")
  validateSingleCase "single-bundle-column-error" (bundleSpecFor 2)
    catalog (actualColumns.take 1) first
    (.error .queryDrift "query drift: prepared bundle has 1 columns; expected 2")
  pure 8

private def benchmarkSpanDecode (_ : TypeResolver) (_ : Array ResolvedType)
    (_ : Array Pg.Protocol.ColumnDesc) (row : Pg.Protocol.DataRowSpans) :
    Except Error Nat :=
  pure row.size

private def benchmarkPreparedDecode (_ : TypeResolver) (_ : Array ResolvedType)
    (_ : Array Pg.Protocol.ColumnDesc) (cells : Array (Option ByteArray)) :
    Except Error Nat :=
  pure cells.size

private def benchmarkGenericDecode (_ : ResolvedCatalog database)
    (_ : Array Pg.Protocol.ColumnDesc) (cells : Array (Option ByteArray)) :
    Except Error Nat :=
  pure cells.size

private def benchmarkSpecFor : DecoderMode → QuerySpec database Unit Nat .many
  | .span => {
      name := "benchmark-span"
      sql := "SELECT left, right"
      contractHash := "benchmark-span"
      params := #[]
      columns := expectedColumns
      encode := fun _ _ => pure { values := #[], formats := #[] }
      decode := benchmarkGenericDecode
      preparedDecode := some benchmarkPreparedDecode
      preparedSpanDecode := some benchmarkSpanDecode
    }
  | .prepared => {
      name := "benchmark-prepared"
      sql := "SELECT left, right"
      contractHash := "benchmark-prepared"
      params := #[]
      columns := expectedColumns
      encode := fun _ _ => pure { values := #[], formats := #[] }
      decode := benchmarkGenericDecode
      preparedDecode := some benchmarkPreparedDecode
    }
  | .generic => {
      name := "benchmark-generic"
      sql := "SELECT left, right"
      contractHash := "benchmark-generic"
      params := #[]
      columns := expectedColumns
      encode := fun _ _ => pure { values := #[], formats := #[] }
      decode := benchmarkGenericDecode
    }

private def benchmarkBundle (bundleExpectedColumns : Nat) :
    PreparedSpanDecoderBundle Nat := {
  expectedColumns := bundleExpectedColumns
  row := benchmarkSpanDecode
  many := guardedPreparedSpanRows bundleExpectedColumns benchmarkSpanDecode
  many_eq_guardedRow := by
    intro resolve types columns rows
    rfl
}

/-- Matching-bundle fixture deliberately retains every legacy callback so an
eager QuerySpec projection is visible in the fixed per-batch counter. -/
private def benchmarkBundleSpec : QuerySpec database Unit Nat .many := {
  benchmarkSpecFor .span with
  name := "benchmark-bundle"
  contractHash := "benchmark-bundle"
  preparedSpanDecoderBundle := some (benchmarkBundle expectedColumns.size)
}

/-- Nonmatching-width control keeps the specification-width row guard while
forcing the staged cold helper on every batch. -/
private def benchmarkBundleMismatchSpec : QuerySpec database Unit Nat .many := {
  benchmarkSpecFor .span with
  name := "benchmark-bundle-mismatch"
  contractHash := "benchmark-bundle-mismatch"
  preparedSpanDecoderBundle := some (benchmarkBundle 1)
}

@[noinline] private def freshRows (rows : @& Array Pg.Protocol.DataRowSpans) :
    Array Pg.Protocol.DataRowSpans :=
  rows

@[noinline] private def freshRow (row : @& Pg.Protocol.DataRowSpans) :
    Pg.Protocol.DataRowSpans :=
  row

@[noinline] private def runReference (spec : QuerySpec database Unit Nat .many)
    (catalog : ResolvedCatalog database)
    (rows : @& Array Pg.Protocol.DataRowSpans) (iterations : Nat) : Except Error UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    let decoded ← decodeReference spec plan catalog actualColumns (freshRows rows)
    for value in decoded do
      checksum := checksum + UInt64.ofNat value
  pure checksum

@[noinline] private def runCandidate (spec : QuerySpec database Unit Nat .many)
    (catalog : ResolvedCatalog database)
    (rows : @& Array Pg.Protocol.DataRowSpans) (iterations : Nat) : Except Error UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    let decoded ← decodeCandidate spec plan catalog actualColumns (freshRows rows)
    for value in decoded do
      checksum := checksum + UInt64.ofNat value
  pure checksum

@[noinline] private def runEager (spec : QuerySpec database Unit Nat .many)
    (catalog : ResolvedCatalog database)
    (rows : @& Array Pg.Protocol.DataRowSpans) (iterations : Nat) : Except Error UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    let decoded ← decodeEagerCandidate spec plan catalog actualColumns (freshRows rows)
    for value in decoded do
      checksum := checksum + UInt64.ofNat value
  pure checksum

@[noinline] private def runSingleProduction
    (spec : QuerySpec database Unit Nat .many)
    (catalog : ResolvedCatalog database)
    (row : @& Pg.Protocol.DataRowSpans) (iterations : Nat) : Except Error UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    let decoded ← PreparedSingleRowDispatchBenchmark.decodeProduction
      spec plan catalog actualColumns (freshRow row)
    checksum := checksum + UInt64.ofNat decoded
  pure checksum

private inductive Mode where
  | reference
  | eager
  | candidate
  | single

private def runIterations (mode : Mode) (spec : QuerySpec database Unit Nat .many)
    (catalog : ResolvedCatalog database)
    (rows : Array Pg.Protocol.DataRowSpans) (iterations : Nat) : Except Error UInt64 :=
  match mode with
  | .reference => runReference spec catalog rows iterations
  | .eager => runEager spec catalog rows iterations
  | .candidate => runCandidate spec catalog rows iterations
  | .single =>
    match rows[0]? with
    | some row => runSingleProduction spec catalog row iterations
    | none => pure 0

private def expectOk (label : String) : Except Error α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {error.toMessage}")

private def parseNatural (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a nonnegative decimal integer")
  pure parsed

private def fixtureRow : Pg.Protocol.DataRowSpans :=
  Pg.Protocol.DataRowSpans.ofCells #[
    some "prepared-dispatch-left".toUTF8,
    some "prepared-dispatch-right".toUTF8
  ]

def runMain (args : List String) : IO Unit := do
  let (modeName, decoderName, pageSize, iterations, warmup) ← match args with
    | [mode, decoder, pageSize, iterations, warmup] =>
      pure (mode, decoder,
        ← parseNatural "page size" pageSize,
        ← parseNatural "iterations" iterations,
        ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: prepared_row_dispatch_benchmark " ++
          "(reference|eager|candidate|single) " ++
          "(bundle|bundle_mismatch|span|prepared|generic) " ++
          "(0|1|55) iterations warmup")
  let mode ← match modeName with
    | "reference" => pure Mode.reference
    | "eager" => pure Mode.eager
    | "candidate" => pure Mode.candidate
    | "single" => pure Mode.single
    | _ => throw (IO.userError
        "mode must be reference, eager, candidate, or single")
  let spec ← match decoderName with
    | "bundle" => pure benchmarkBundleSpec
    | "bundle_mismatch" => pure benchmarkBundleMismatchSpec
    | "span" => pure (benchmarkSpecFor .span)
    | "prepared" => pure (benchmarkSpecFor .prepared)
    | "generic" => pure (benchmarkSpecFor .generic)
    | _ => throw (IO.userError
        "decoder must be bundle, bundle_mismatch, span, prepared, or generic")
  unless pageSize == 0 || pageSize == 1 || pageSize == 55 do
    throw (IO.userError "page size must be 0, 1, or 55")
  match mode with
  | .single =>
    unless pageSize == 1 do
      throw (IO.userError "single mode requires page size 1")
  | _ => pure ()
  let catalog ← expectOk "catalog fixture" catalogResult
  let legacyCases ← validateSemantics catalog
  let bundleCases ← validateBundleSemantics catalog
  let singleCases ← validateSingleSemantics catalog
  let rows := Array.replicate pageSize fixtureRow
  let expectedWarmup := UInt64.ofNat (pageSize * 2 * warmup)
  let warmupChecksum ← expectOk "warmup" <|
    runIterations mode spec catalog rows warmup
  unless warmupChecksum == expectedWarmup do
    throw (IO.userError "warmup checksum mismatch")
  let expected := UInt64.ofNat (pageSize * 2 * iterations)
  let checksum ← expectOk "measured" <|
    runIterations mode spec catalog rows iterations
  unless checksum == expected do
    throw (IO.userError "measured checksum mismatch")
  IO.println <| s!"benchmark=pgx_prepared_row_dispatch_v5 mode={modeName} decoder={decoderName} " ++
    s!"page_size={pageSize} iterations={iterations} warmup={warmup} checksum={checksum}"
  IO.println <| s!"prepared_row_dispatch_validation=pass cases={legacyCases + bundleCases + singleCases} " ++
    s!"single_cases={singleCases} selectors=reference,eager,candidate,single " ++
    "decoders=bundle,bundle_mismatch,span,prepared,generic " ++
    "malformed=pass first_error=pass escape=pass"

end Pgx.Typed.PreparedRowDispatchBenchmarkHarness

def main (args : List String) : IO Unit :=
  Pgx.Typed.PreparedRowDispatchBenchmarkHarness.runMain args
