import Pgx.Typed.Descriptors

/-!
Focused benchmark for the prepared built-in decoder's borrowed cell payload.
The exported monomorphic legacy oracles own each `Option ByteArray`, forcing
the pre-change increment/decrement around generated `values[i]!` expressions.
The cell-size pair isolates that ABI cost; the decoder pairs report its effect
in representative binary and mixed rows without imposing a noise-sensitive
throughput gate.
-/

open Pgx.Typed

private abbrev Values := Array (Option ByteArray)

@[noinline, export pgx_benchmark_legacy_cell_size] private opaque
    legacyCellSize (value : Option ByteArray) : Nat :=
  match value with
  | none => 0
  | some bytes => bytes.size

@[noinline] private def borrowedCellSize (value : @& Option ByteArray) : Nat :=
  match value with
  | none => 0
  | some bytes => bytes.size

@[noinline, export pgx_benchmark_legacy_decode_int64] private opaque
    legacyDecodeInt64 (typeOid : UInt32) (format : UInt16)
    (value : Option ByteArray) : Except Error Int64 :=
  match Pg.decodeValue (α := Int64) typeOid format value with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

@[noinline, export pgx_benchmark_legacy_decode_string] private opaque
    legacyDecodeString (typeOid : UInt32) (format : UInt16)
    (value : Option ByteArray) : Except Error String :=
  match Pg.decodeValue (α := String) typeOid format value with
  | .ok decoded => pure decoded
  | .error message => throw (.decode message)

@[noinline] private def legacyBinaryRow (values : @& Values) : Except Error Nat := do
  let id ← legacyDecodeInt64 Pg.Oid.int8 1 values[0]!
  let owner ← legacyDecodeInt64 Pg.Oid.int8 1 values[1]!
  let quantity ← legacyDecodeInt64 Pg.Oid.int8 1 values[4]!
  pure (id.toInt.natAbs + owner.toInt.natAbs + quantity.toInt.natAbs)

@[noinline] private def borrowedBinaryRow (values : @& Values) : Except Error Nat := do
  let id ← decodePlannedBuiltin (α := Int64) Pg.Oid.int8 1 values[0]!
  let owner ← decodePlannedBuiltin (α := Int64) Pg.Oid.int8 1 values[1]!
  let quantity ← decodePlannedBuiltin (α := Int64) Pg.Oid.int8 1 values[4]!
  pure (id.toInt.natAbs + owner.toInt.natAbs + quantity.toInt.natAbs)

@[noinline] private def legacyAbiRow (values : @& Values) : Except Error Nat :=
  pure <| legacyCellSize values[0]! + legacyCellSize values[1]! +
    legacyCellSize values[2]! + legacyCellSize values[3]! +
    legacyCellSize values[4]! + legacyCellSize values[5]!

@[noinline] private def borrowedAbiRow (values : @& Values) : Except Error Nat :=
  pure <| borrowedCellSize values[0]! + borrowedCellSize values[1]! +
    borrowedCellSize values[2]! + borrowedCellSize values[3]! +
    borrowedCellSize values[4]! + borrowedCellSize values[5]!

@[noinline] private def legacyMixedRow (values : @& Values) : Except Error Nat := do
  let numeric ← legacyBinaryRow values
  let name ← legacyDecodeString Pg.Oid.text 0 values[2]!
  let sku ← legacyDecodeString Pg.Oid.text 0 values[3]!
  let description ← legacyDecodeString Pg.Oid.text 0 values[5]!
  pure (numeric + name.utf8ByteSize + sku.utf8ByteSize + description.utf8ByteSize)

@[noinline] private def borrowedMixedRow (values : @& Values) : Except Error Nat := do
  let numeric ← borrowedBinaryRow values
  let name ← decodePlannedBuiltin (α := String) Pg.Oid.text 0 values[2]!
  let sku ← decodePlannedBuiltin (α := String) Pg.Oid.text 0 values[3]!
  let description ← decodePlannedBuiltin (α := String) Pg.Oid.text 0 values[5]!
  pure (numeric + name.utf8ByteSize + sku.utf8ByteSize + description.utf8ByteSize)

private def runRows (decode : @& Values → Except Error Nat)
    (values : @& Values) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match decode values with
    | .ok value => checksum := checksum + value
    | .error error => throw (IO.userError error.toMessage)
  pure checksum

private def measureDecoder (decode : @& Values → Except Error Nat)
    (values : @& Values) (iterations : Nat) : IO (Nat × Nat) := do
  discard <| runRows decode values (Nat.min iterations 1000)
  let started ← IO.monoNanosNow
  let checksum ← runRows decode values iterations
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

private def report (label : String) (iterations : Nat)
    (legacySamples borrowedSamples : Array Nat) : IO Unit := do
  let legacy := median legacySamples
  let borrowed := median borrowedSamples
  let legacyPerRow := if iterations == 0 then 0 else legacy * 100 / iterations
  let borrowedPerRow := if iterations == 0 then 0 else borrowed * 100 / iterations
  let speedup := if borrowed == 0 then 0 else legacy * 100 / borrowed
  IO.println s!"{label}_legacy_samples_ns={formatSamples legacySamples}"
  IO.println s!"{label}_borrowed_samples_ns={formatSamples borrowedSamples}"
  IO.println s!"{label}_legacy_median_ns_per_row={formatHundredths legacyPerRow}"
  IO.println s!"{label}_borrowed_median_ns_per_row={formatHundredths borrowedPerRow}"
  IO.println s!"{label}_speedup_x={formatHundredths speedup}"

private def parseNat (value? : Option String) (fallback : Nat) : Nat :=
  (value? >>= String.toNat?).getD fallback

private def benchmark (values : @& Values) (iterations rounds : Nat) : IO Unit := do
  let mut abiLegacy := #[]
  let mut abiBorrowed := #[]
  let mut binaryLegacy := #[]
  let mut binaryBorrowed := #[]
  let mut mixedLegacy := #[]
  let mut mixedBorrowed := #[]
  for round in [0:rounds] do
    let reverse := round % 2 == 1
    let measurePair legacy borrowed := do
      if reverse then
        let borrowedResult ← measureDecoder borrowed values iterations
        let legacyResult ← measureDecoder legacy values iterations
        pure (legacyResult, borrowedResult)
      else
        let legacyResult ← measureDecoder legacy values iterations
        let borrowedResult ← measureDecoder borrowed values iterations
        pure (legacyResult, borrowedResult)
    let abi ← measurePair legacyAbiRow borrowedAbiRow
    unless abi.1.2 == abi.2.2 do
      throw (IO.userError "ABI benchmark checksums differ")
    abiLegacy := abiLegacy.push abi.1.1
    abiBorrowed := abiBorrowed.push abi.2.1
    let binary ← measurePair legacyBinaryRow borrowedBinaryRow
    unless binary.1.2 == binary.2.2 do
      throw (IO.userError "binary-row benchmark checksums differ")
    binaryLegacy := binaryLegacy.push binary.1.1
    binaryBorrowed := binaryBorrowed.push binary.2.1
    let mixed ← measurePair legacyMixedRow borrowedMixedRow
    unless mixed.1.2 == mixed.2.2 do
      throw (IO.userError "mixed-row benchmark checksums differ")
    mixedLegacy := mixedLegacy.push mixed.1.1
    mixedBorrowed := mixedBorrowed.push mixed.2.1
  report "abi" iterations abiLegacy abiBorrowed
  report "binary" iterations binaryLegacy binaryBorrowed
  report "mixed" iterations mixedLegacy mixedBorrowed

def main (args : List String) : IO Unit := do
  let iterations := parseNat args.head? 500000
  let rounds := Nat.max 3 (parseNat (args.drop 1).head? 7)
  let values : Values := #[
    some (Pg.putInt64BE 123456789),
    some (Pg.putInt64BE 7),
    some "widget-name".toUTF8,
    some "SKU-12345".toUTF8,
    some (Pg.putInt64BE 42),
    some "representative widget description".toUTF8
  ]
  -- `IO.asTask` marks the captured graph as multi-threaded, matching the
  -- socket-task-to-handler ownership boundary seen in the service profile.
  let task ← IO.asTask (benchmark values iterations rounds)
  match ← IO.wait task with
  | .ok () => pure ()
  | .error error => throw error
  unless values.size == 6 do
    throw (IO.userError "benchmark input was unexpectedly consumed")
  IO.println "borrowed decoder benchmark completed"
