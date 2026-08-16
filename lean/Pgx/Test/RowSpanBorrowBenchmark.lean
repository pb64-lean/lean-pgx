import Pgx.Typed.Query

/-!
Focused checkpoint for ownership at `fetchMany`'s retained-span decoder
callback.  The timing case uses the same named mapping boundary as production;
the semantic controls cover materialization, errors, and values that escape a
borrowed decoder.
-/

open Pgx.Typed

private abbrev SpanRow := Pg.Protocol.DataRowSpans

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
  let materialized ← expectOk "materialize control" <|
    Internal.decodeSpanRows materializeRow #[Pg.Protocol.DataRowSpans.ofCells cells]
  unless materialized == #[cells] do
    throw (IO.userError "materialized row did not survive the callback boundary")

  let escaped ← expectOk "span escape control" <|
    Internal.decodeSpanRows escapeRow #[Pg.Protocol.DataRowSpans.ofCells cells]
  let escapedCells := escaped.map (·.materialize)
  unless escapedCells == #[cells] do
    throw (IO.userError "escaped span row did not retain its payload")

  let rows := #[
    Pg.Protocol.DataRowSpans.ofCells #[some "accept".toUTF8],
    Pg.Protocol.DataRowSpans.ofCells #[some "reject".toUTF8],
    Pg.Protocol.DataRowSpans.ofCells #[some "unreached".toUTF8]
  ]
  match Internal.decodeSpanRows rejectSentinel rows with
  | .ok _ => throw (IO.userError "error control unexpectedly decoded every row")
  | .error error =>
    unless error.kind == .decode &&
        error.toMessage == "row decoding failed: row-span sentinel rejected" do
      throw (IO.userError s!"error control changed failure: {error.toMessage}")

private def runBatches (row : @& SpanRow) (pageSize iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let rows := Array.replicate pageSize row
    let decoded ← expectOk "benchmark decode" <|
      Internal.decodeSpanRows rowSize rows
    checksum := checksum + decoded.foldl (· + ·) 0
  pure checksum

private def measureRun (row : @& SpanRow)
    (pageSize iterations : Nat) : IO (Nat × Nat) := do
  discard <| runBatches row pageSize (Nat.min iterations 1000)
  let started ← IO.monoNanosNow
  let checksum ← runBatches row pageSize iterations
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
    let mut samples := #[]
    let mut expectedChecksum : Option Nat := none
    for _ in [0:rounds] do
      let sample ← measureRun row pageSize iterations
      match expectedChecksum with
      | none => expectedChecksum := some sample.2
      | some expected => unless sample.2 == expected do
          throw (IO.userError "benchmark checksum changed between rounds")
      samples := samples.push sample.1
    let totalRows := pageSize * iterations
    let nanosPerRow := if totalRows == 0 then 0 else median samples * 100 / totalRows
    IO.println s!"page_{pageSize}_samples_ns={formatSamples samples}"
    IO.println s!"page_{pageSize}_median_ns_per_row={formatHundredths nanosPerRow}"
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
