import Pgx.Typed.Query

/-!
Focused differential benchmark for prepared-parameter admission.

The reference reproduces the former `runChecked` shape: it lifts the encoder's
`Except` success into `Async`, binds it, then lifts successful parameter
validation into another resolved `Async` action and binds again. The candidate
keeps both synchronous branches nested and reaches the same no-inline finish
action directly. Preparation, encoding, PostgreSQL execution, I/O, and row
decoding are outside the measured region.
-/

namespace Pgx.Typed.ParameterAdmissionBenchmark

open Std.Async

@[noinline] private def freshEncodedResult (encoded : @& EncodedParams) :
    Except Error EncodedParams :=
  .ok encoded

@[noinline] private def finish (encoded : EncodedParams) :
    Async (Except Error EncodedParams) :=
  pure (.ok encoded)

@[noinline] private def admitReference (expected : Nat)
    (encodedResult : Except Error EncodedParams) :
    Async (Except Error EncodedParams) := do
  let encoded ← match encodedResult with
    | .error error => return .error error
    | .ok encoded => pure encoded
  match ParameterValidationBenchmark.validateCandidate expected encoded with
  | .error error => return .error error
  | .ok () => pure ()
  finish encoded

@[noinline] private def admitCandidate (expected : Nat)
    (encodedResult : Except Error EncodedParams) :
    Async (Except Error EncodedParams) :=
  match encodedResult with
  | .error error => pure (.error error)
  | .ok encoded =>
    match ParameterValidationBenchmark.validateCandidate expected encoded with
    | .error error => pure (.error error)
    | .ok () => finish encoded

private def payload (index : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((index * 31 + 7) % 256),
    UInt8.ofNat ((index * 67 + 11) % 256),
    UInt8.ofNat ((index * 101 + 13) % 256)]

private def encodedWith (valueCount : Nat) (formats : Array UInt16) : EncodedParams := {
  values := (Array.range valueCount).map fun index => some (payload index)
  formats
}

private def mixedFormats (count : Nat) : Array UInt16 :=
  (Array.range count).map fun index => if index % 2 == 0 then 1 else 0

private def validEncoded (count : Nat) : EncodedParams :=
  encodedWith count (mixedFormats count)

private structure SemanticCase where
  label : String
  expectedCount : Nat
  encodedResult : Except Error EncodedParams
  expected : Except Error EncodedParams

private def validCase (label : String) (count : Nat) (formats : Array UInt16) :
    SemanticCase :=
  let encoded := encodedWith count formats
  { label, expectedCount := count, encodedResult := .ok encoded, expected := .ok encoded }

private def invalidCase (label : String) (expectedCount valueCount : Nat)
    (formats : Array UInt16) (message : String) : SemanticCase :=
  let encoded := encodedWith valueCount formats
  {
    label
    expectedCount
    encodedResult := .ok encoded
    expected := .error (.encode message)
  }

private def semanticCases : Array SemanticCase := #[]
  |>.push (validCase "valid-empty" 0 #[])
  |>.push (validCase "valid-one" 1 (mixedFormats 1))
  |>.push (validCase "valid-two" 2 (mixedFormats 2))
  |>.push (validCase "valid-five" 5 (mixedFormats 5))
  |>.push (validCase "valid-six" 6 (mixedFormats 6))
  |>.push (validCase "valid-all-text" 6 (Array.replicate 6 0))
  |>.push (validCase "valid-all-binary" 6 (Array.replicate 6 1))
  |>.push {
    label := "encoder-error"
    expectedCount := 2
    encodedResult := .error (.encode "encoder rejected fixture")
    expected := .error (.encode "encoder rejected fixture")
  }
  |>.push (invalidCase "value-count-first" 2 1 #[9]
    "generated encoder returned 1 values for 2 parameters")
  |>.push (invalidCase "format-count-second" 2 2 #[9]
    "generated encoder returned 1 formats for 2 parameters")
  |>.push (invalidCase "invalid-first" 5 5 #[9, 0, 1, 7, 0]
    "unsupported PostgreSQL parameter format 9")
  |>.push (invalidCase "invalid-middle" 5 5 #[0, 1, 7, 9, 0]
    "unsupported PostgreSQL parameter format 7")
  |>.push (invalidCase "invalid-last" 5 5 #[0, 1, 0, 1, 65535]
    "unsupported PostgreSQL parameter format 65535")

private def exactResultEq : Except Error EncodedParams →
    Except Error EncodedParams → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right =>
    left.kind == right.kind && left.toMessage == right.toMessage
  | _, _ => false

private def validateSemantics : IO Nat := do
  for fixture in semanticCases do
    let reference ← Async.block
      (admitReference fixture.expectedCount fixture.encodedResult)
    let candidate ← Async.block
      (admitCandidate fixture.expectedCount fixture.encodedResult)
    unless exactResultEq reference fixture.expected do
      throw (IO.userError s!"{fixture.label}: reference differs from expected")
    unless exactResultEq candidate fixture.expected do
      throw (IO.userError s!"{fixture.label}: candidate differs from expected")
    unless exactResultEq reference candidate do
      throw (IO.userError s!"{fixture.label}: reference and candidate differ")
  pure semanticCases.size

@[inline] private def encodedDigest (encoded : @& EncodedParams) : UInt64 := Id.run do
  let mut digest := UInt64.ofNat encoded.values.size + 1469598103934665603
  for value in encoded.values do
    match value with
    | none => digest := digest * 1099511628211 + 1
    | some bytes =>
      digest := digest * 1099511628211 + UInt64.ofNat bytes.size + 2
      for byte in bytes do
        digest := digest * 1099511628211 + UInt64.ofNat byte.toNat + 1
  for format in encoded.formats do
    digest := digest * 1099511628211 + UInt64.ofNat format.toNat + 1
  return digest

@[noinline] private def runReference (expected : Nat) (encoded : @& EncodedParams)
    (iterations : Nat) : Async UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    match ← admitReference expected (freshEncodedResult encoded) with
    | .error error => throw (IO.userError error.toMessage)
    | .ok admitted => checksum := checksum + encodedDigest admitted
  pure checksum

@[noinline] private def runCandidate (expected : Nat) (encoded : @& EncodedParams)
    (iterations : Nat) : Async UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    match ← admitCandidate expected (freshEncodedResult encoded) with
    | .error error => throw (IO.userError error.toMessage)
    | .ok admitted => checksum := checksum + encodedDigest admitted
  pure checksum

private inductive Mode where
  | reference
  | candidate

private def runIterations (mode : Mode) (expected : Nat)
    (encoded : @& EncodedParams) (iterations : Nat) : Async UInt64 :=
  match mode with
  | .reference => runReference expected encoded iterations
  | .candidate => runCandidate expected encoded iterations

private def parseNatural (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a nonnegative decimal integer")
  pure parsed

private def supportedCount (count : Nat) : Bool :=
  count == 0 || count == 1 || count == 2 || count == 5 || count == 6

def runMain (args : List String) : IO Unit := do
  let (modeName, count, iterations, warmup) ← match args with
    | [mode, count, iterations, warmup] =>
      pure (mode,
        ← parseNatural "count" count,
        ← parseNatural "iterations" iterations,
        ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: parameter_admission_benchmark (reference|candidate) " ++
          "(0|1|2|5|6) iterations warmup")
  let mode ← match modeName with
    | "reference" => pure Mode.reference
    | "candidate" => pure Mode.candidate
    | _ => throw (IO.userError "mode must be reference or candidate")
  unless supportedCount count do
    throw (IO.userError s!"unsupported parameter count {count}; expected 0, 1, 2, 5, or 6")

  let cases ← validateSemantics
  let encoded := validEncoded count
  let digest := encodedDigest encoded
  unless digest != 0 do
    throw (IO.userError "selected fixture digest is zero")
  let warmupChecksum ← Async.block (runIterations mode count encoded warmup)
  unless warmupChecksum == digest * UInt64.ofNat warmup do
    throw (IO.userError "warmup checksum mismatch")
  let checksum ← Async.block (runIterations mode count encoded iterations)
  unless checksum == digest * UInt64.ofNat iterations do
    throw (IO.userError "measured checksum mismatch")
  IO.println <| s!"benchmark=pgx_parameter_admission_v1 mode={modeName} " ++
    s!"count={count} iterations={iterations} warmup={warmup} checksum={checksum}"
  IO.println <| s!"parameter_admission_validation=pass cases={cases} " ++
    "result=exact reference=candidate expected=pass"

end Pgx.Typed.ParameterAdmissionBenchmark

def main (args : List String) : IO Unit :=
  Pgx.Typed.ParameterAdmissionBenchmark.runMain args
