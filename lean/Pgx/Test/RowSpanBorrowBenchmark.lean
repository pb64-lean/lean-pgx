import Pgx.Typed.Query

/-!
Focused checkpoint for ownership at `fetchMany`'s retained-span decoder
callback.  It models both dynamic calls in the production path: `Array.mapM`
to `decodeRow`, then `decodeRow` to the callback stored in `QuerySpec`.  The
semantic controls cover materialization, errors, and values that escape a
borrowed decoder.
-/

open Pgx.Typed

private abbrev SpanRow := Pg.Protocol.DataRowSpans

/-- Existing ownership shape: the outer dispatcher consumes the row and can
transfer it to the dynamically stored decoder without another retain. -/
@[noinline] private def dispatchOwned
    (decode : SpanRow → Except Error Row) (row : SpanRow) : Except Error Row :=
  decode row

@[noinline] private def decodeSpanRowsOwned
    (decode : SpanRow → Except Error Row)
    (rows : Array SpanRow) : Except Error (Array Row) :=
  rows.mapM (dispatchOwned decode)

/-- Rejected source-level candidate.  Dynamic closure application still uses
the consuming boxed ABI, so each `@&` layer must retain before forwarding. -/
@[noinline] private def dispatchBorrowed
    (decode : @& SpanRow → Except Error Row)
    (row : @& SpanRow) : Except Error Row :=
  decode row

@[noinline] private def decodeSpanRowsBorrowed
    (decode : @& SpanRow → Except Error Row)
    (rows : Array SpanRow) : Except Error (Array Row) :=
  rows.mapM (dispatchBorrowed decode)

@[noinline] private def rowSize (row : @& SpanRow) : Except Error Nat :=
  pure row.size

@[noinline] private def materializeRow
    (row : @& SpanRow) : Except Error (Array (Option ByteArray)) :=
  pure row.materialize

@[noinline] private def escapeRow (row : @& SpanRow) : Except Error SpanRow :=
  pure row

@[noinline] private def rejectSentinel (row : @& SpanRow) : Except Error Nat := do
  let some (some value) := row.cell? 0
    | throw (.decode "missing sentinel cell")
  if value == "reject".toUTF8 then
    throw (.decode "row-span sentinel rejected")
  pure value.size

private def expectOk {α : Type} (context : String) : Except Error α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error.toMessage}")

private def semanticControls : IO Unit := do
  let cells := #[some "alpha".toUTF8, none, some "omega".toUTF8]
  let checkSuccess (label : String)
      (materializedResult : Except Error (Array (Array (Option ByteArray))))
      (escapedResult : Except Error (Array SpanRow)) : IO Unit := do
    let materialized ← expectOk s!"{label} materialize control" materializedResult
    unless materialized == #[cells] do
      throw (IO.userError s!"{label} materialized row did not survive")
    let escaped ← expectOk s!"{label} span escape control" escapedResult
    unless escaped.map (·.materialize) == #[cells] do
      throw (IO.userError s!"{label} escaped span row did not retain its payload")
  checkSuccess "owned"
    (decodeSpanRowsOwned materializeRow #[Pg.Protocol.DataRowSpans.ofCells cells])
    (decodeSpanRowsOwned escapeRow #[Pg.Protocol.DataRowSpans.ofCells cells])
  checkSuccess "borrowed"
    (decodeSpanRowsBorrowed materializeRow #[Pg.Protocol.DataRowSpans.ofCells cells])
    (decodeSpanRowsBorrowed escapeRow #[Pg.Protocol.DataRowSpans.ofCells cells])

  let sentinelRows : Unit → Array SpanRow := fun _ => #[
      Pg.Protocol.DataRowSpans.ofCells #[some "accept".toUTF8],
      Pg.Protocol.DataRowSpans.ofCells #[some "reject".toUTF8],
      Pg.Protocol.DataRowSpans.ofCells #[some "unreached".toUTF8]
    ]
  let checkError (label : String) : Except Error (Array Nat) → IO Unit
    | .ok _ => throw (IO.userError s!"{label} unexpectedly decoded every row")
    | .error error =>
      unless error.kind == .decode &&
          error.toMessage == "row decoding failed: row-span sentinel rejected" do
        throw (IO.userError s!"{label} changed failure: {error.toMessage}")
  checkError "owned error control" <|
    decodeSpanRowsOwned rejectSentinel (sentinelRows ())
  checkError "borrowed error control" <|
    decodeSpanRowsBorrowed rejectSentinel (sentinelRows ())

private def runOwnedBatches
    (row : @& SpanRow) (pageSize iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let rows := Array.replicate pageSize row
    let decoded ← expectOk "benchmark decode" <|
      decodeSpanRowsOwned rowSize rows
    checksum := checksum + decoded.foldl (· + ·) 0
  pure checksum

private def runBorrowedBatches
    (row : @& SpanRow) (pageSize iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let rows := Array.replicate pageSize row
    let decoded ← expectOk "benchmark decode" <|
      decodeSpanRowsBorrowed rowSize rows
    checksum := checksum + decoded.foldl (· + ·) 0
  pure checksum

private def measureRun (run : @& SpanRow → Nat → Nat → IO Nat)
    (row : @& SpanRow) (pageSize iterations : Nat) : IO (Nat × Nat) := do
  discard <| run row pageSize (Nat.min iterations 1000)
  let started ← IO.monoNanosNow
  let checksum ← run row pageSize iterations
  pure ((← IO.monoNanosNow) - started, checksum)

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value <= head then value :: head :: tail else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def parseNat (value? : Option String) (fallback : Nat) : Nat :=
  (value? >>= String.toNat?).getD fallback

private def benchmark (row : @& SpanRow) (iterations rounds : Nat) : IO Unit := do
  for pageSize in #[1, 55] do
    let mut ownedSamples := #[]
    let mut borrowedSamples := #[]
    let mut expectedChecksum : Option Nat := none
    for round in [0:rounds] do
      let measurePair := if round % 2 == 0 then do
          let owned ← measureRun runOwnedBatches row pageSize iterations
          let borrowed ← measureRun runBorrowedBatches row pageSize iterations
          pure (owned, borrowed)
        else do
          let borrowed ← measureRun runBorrowedBatches row pageSize iterations
          let owned ← measureRun runOwnedBatches row pageSize iterations
          pure (owned, borrowed)
      let pair ← measurePair
      unless pair.1.2 == pair.2.2 do
        throw (IO.userError "owned and borrowed checksums differ")
      match expectedChecksum with
      | none => expectedChecksum := some pair.1.2
      | some expected => unless pair.1.2 == expected do
          throw (IO.userError "benchmark checksum changed between rounds")
      ownedSamples := ownedSamples.push pair.1.1
      borrowedSamples := borrowedSamples.push pair.2.1
    let totalRows := pageSize * iterations
    let ownedMedian := median ownedSamples
    let borrowedMedian := median borrowedSamples
    let ownedPerRow := if totalRows == 0 then 0 else ownedMedian * 100 / totalRows
    let borrowedPerRow := if totalRows == 0 then 0 else borrowedMedian * 100 / totalRows
    let speedup := if borrowedMedian == 0 then 0 else ownedMedian * 100 / borrowedMedian
    IO.println s!"page_{pageSize}_owned_samples_ns={formatSamples ownedSamples}"
    IO.println s!"page_{pageSize}_borrowed_samples_ns={formatSamples borrowedSamples}"
    IO.println s!"page_{pageSize}_owned_median_ns_per_row={formatHundredths ownedPerRow}"
    IO.println s!"page_{pageSize}_borrowed_median_ns_per_row={formatHundredths borrowedPerRow}"
    IO.println s!"page_{pageSize}_borrowed_speedup_x={formatHundredths speedup}"
    IO.println s!"page_{pageSize}_checksum={expectedChecksum.getD 0}"

def main (args : List String) : IO Unit := do
  let iterations := parseNat args.head? 100000
  let rounds := Nat.max 3 (parseNat (args.drop 1).head? 7)
  semanticControls
  let row := Pg.Protocol.DataRowSpans.ofCells #[
    some "widget-name".toUTF8,
    some (Pg.putInt64BE 42),
    none,
    some "representative widget description".toUTF8
  ]
  -- Match the service's socket-task-to-handler ownership boundary.
  let task ← IO.asTask (benchmark row iterations rounds)
  match ← IO.wait task with
  | .ok () => pure ()
  | .error error => throw error
  unless row.size == 4 do
    throw (IO.userError "benchmark input was unexpectedly consumed")
  IO.println "row-span callback benchmark completed"
