import Pgx.Typed.Query

/-!
Focused differential benchmark for prepared-parameter admission validation.

The reference preserves the validation as it appears in `runChecked`: because
the loop is written in the surrounding `Async` computation, every valid
format is sequenced through `Async.bind`.  The candidate is the pure production
helper, wrapped in one already-resolved `Async` action so both benchmark modes
cross the same `Async.block` boundary.
-/

namespace Pgx.Typed.ParameterValidationBenchmark

open Std.Async

private def validateReference (expected : Nat) (encoded : @& EncodedParams) :
    Async (Except Error Unit) := do
  unless encoded.values.size == expected do
    return .error (.encode
      s!"generated encoder returned {encoded.values.size} values for {expected} parameters")
  unless encoded.formats.size == expected do
    return .error (.encode
      s!"generated encoder returned {encoded.formats.size} formats for {expected} parameters")
  for format in encoded.formats do
    unless format == 0 || format == 1 do
      return .error (.encode s!"unsupported PostgreSQL parameter format {format}")
  pure (.ok ())

private def validateCandidateAsync (expected : Nat) (encoded : @& EncodedParams) :
    Async (Except Error Unit) :=
  pure (validateCandidate expected encoded)

private def validEncoded (count : Nat) : EncodedParams := {
  values := Array.replicate count none
  formats := (Array.range count).map fun index =>
    if index % 2 == 0 then (1 : UInt16) else 0
}

private def encodedWith (valueCount : Nat) (formats : Array UInt16) : EncodedParams := {
  values := Array.replicate valueCount none
  formats
}

private structure Fixture where
  label : String
  expected : Nat
  encoded : EncodedParams
  errorMessage? : Option String := none

private def fixtures : Array Fixture := #[
  { label := "valid-empty", expected := 0, encoded := validEncoded 0 },
  { label := "valid-one", expected := 1, encoded := validEncoded 1 },
  { label := "valid-two", expected := 2, encoded := validEncoded 2 },
  { label := "valid-five", expected := 5, encoded := validEncoded 5 },
  { label := "valid-six", expected := 6, encoded := validEncoded 6 },
  {
    label := "value-count-first"
    expected := 2
    encoded := encodedWith 1 #[9]
    errorMessage? := some
      "parameter encoding failed: generated encoder returned 1 values for 2 parameters"
  },
  {
    label := "format-count-second"
    expected := 2
    encoded := encodedWith 2 #[9]
    errorMessage? := some
      "parameter encoding failed: generated encoder returned 1 formats for 2 parameters"
  },
  {
    label := "invalid-first"
    expected := 5
    encoded := encodedWith 5 #[9, 0, 1, 7, 0]
    errorMessage? := some
      "parameter encoding failed: unsupported PostgreSQL parameter format 9"
  },
  {
    label := "invalid-middle"
    expected := 5
    encoded := encodedWith 5 #[0, 1, 7, 9, 0]
    errorMessage? := some
      "parameter encoding failed: unsupported PostgreSQL parameter format 7"
  },
  {
    label := "invalid-last"
    expected := 5
    encoded := encodedWith 5 #[0, 1, 0, 1, 65535]
    errorMessage? := some
      "parameter encoding failed: unsupported PostgreSQL parameter format 65535"
  }
]

private def checkExpected (fixture : @& Fixture) : Except Error Unit → IO Unit
  | .ok () =>
      if fixture.errorMessage?.isNone then
        pure ()
      else
        throw (IO.userError s!"{fixture.label}: expected validation to fail")
  | .error error =>
      match fixture.errorMessage? with
      | none => throw (IO.userError
          s!"{fixture.label}: validation unexpectedly failed: {error.toMessage}")
      | some expected =>
          unless error.kind == .encode && error.toMessage == expected do
            throw (IO.userError
              s!"{fixture.label}: expected '{expected}', got '{error.toMessage}'")

private def checkSame (fixture : @& Fixture)
    (reference candidate : Except Error Unit) : IO Unit := do
  match reference, candidate with
  | .ok (), .ok () => pure ()
  | .error left, .error right =>
      unless left.kind == right.kind && left.toMessage == right.toMessage do
        throw (IO.userError
          s!"{fixture.label}: reference/candidate errors differ: '{left.toMessage}' / '{right.toMessage}'")
  | .ok (), .error error => throw (IO.userError
      s!"{fixture.label}: candidate alone failed: {error.toMessage}")
  | .error error, .ok () => throw (IO.userError
      s!"{fixture.label}: reference alone failed: {error.toMessage}")

private def semanticControls : IO Unit := do
  for fixture in fixtures do
    let reference ← Async.block (validateReference fixture.expected fixture.encoded)
    let candidate := validateCandidate fixture.expected fixture.encoded
    checkSame fixture reference candidate
    checkExpected fixture reference

private inductive Mode where
  | reference
  | candidate

private def parseMode : String → Option Mode
  | "reference" => some .reference
  | "candidate" => some .candidate
  | _ => none

private def validator : Mode → Nat → @& EncodedParams → Async (Except Error Unit)
  | .reference => validateReference
  | .candidate => validateCandidateAsync

private def run (validate : Nat → @& EncodedParams → Async (Except Error Unit))
    (expected : Nat) (encoded : @& EncodedParams) (iterations : Nat) : Async Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match ← validate expected encoded with
    | .ok () => checksum := checksum + expected + encoded.formats.size + 1
    | .error error => throw (IO.userError error.toMessage)
  pure checksum

private def supportedCount (count : Nat) : Bool :=
  count == 0 || count == 1 || count == 2 || count == 5 || count == 6

def runMain (args : List String) : IO Unit := do
  semanticControls
  let modeText := args.head?.getD "candidate"
  let some mode := parseMode modeText
    | throw (IO.userError s!"unknown parameter-validation mode: {modeText}")
  let count := ((args.drop 1).head? >>= String.toNat?).getD 5
  unless supportedCount count do
    throw (IO.userError
      s!"unsupported parameter count {count}; expected one of 0, 1, 2, 5, or 6")
  let iterations := ((args.drop 2).head? >>= String.toNat?).getD 1000000
  let warmup := ((args.drop 3).head? >>= String.toNat?).getD 100
  let encoded := validEncoded count
  let validate := validator mode
  let _ ← Async.block (run validate count encoded warmup)
  let checksum ← Async.block (run validate count encoded iterations)
  IO.println
    s!"mode={modeText} count={count} iterations={iterations} checksum={checksum}"

end Pgx.Typed.ParameterValidationBenchmark

def main (args : List String) : IO Unit :=
  Pgx.Typed.ParameterValidationBenchmark.runMain args
