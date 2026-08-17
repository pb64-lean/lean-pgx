import Pgx.Typed.Descriptors

/-!
Focused differential benchmark for prepared result-column verification.

The reference is the former Range/indexed production loop. The candidate is
the exact proof-bounded native-`USize` implementation used by compiled
production. The measured success path obtains fresh ownership of both arrays
on every iteration. A full digest of every expected and actual descriptor
field is computed once before measurement; each successful verifier call then
accumulates only that constant-size digest token. Preparation, PostgreSQL
execution, I/O, and row decoding are outside the measured region.
-/

namespace Pgx.Typed.PreparedColumnVerificationBenchmarkHarness

open PreparedColumnVerificationBenchmark

private def expectedColumn (index : Nat) : PreparedColumnPlan := {
  name := s!"column_{index + 1}"
  typeOid := UInt32.ofNat (23 + index * 17)
  typeMod := if index % 3 == 0 then Int32.ofInt (-1) else Int32.ofInt (index + 4)
  origin := if index % 2 == 0 then
    some { tableOid := UInt32.ofNat (90001 + index), attnum := UInt16.ofNat (index + 1) }
  else
    none
  format := UInt16.ofNat (index % 2)
}

private def actualColumn (expected : PreparedColumnPlan) : Pg.Protocol.ColumnDesc := {
  name := expected.name
  tableOid := expected.origin.map (·.tableOid) |>.getD 777777
  attnum := expected.origin.map (·.attnum) |>.getD 444
  typeOid := expected.typeOid
  typeSize := Int16.ofInt (-1)
  typeMod := expected.typeMod
  format := expected.format
}

private def expectedColumns (count : Nat) : Array PreparedColumnPlan :=
  (Array.range count).map expectedColumn

private def actualColumns (expected : Array PreparedColumnPlan) :
    Array Pg.Protocol.ColumnDesc :=
  expected.map actualColumn

private def expectedColumnsWithOrigins (count : Nat) : Array PreparedColumnPlan :=
  (Array.range count).map fun index =>
    { expectedColumn index with origin := some {
        tableOid := UInt32.ofNat (90001 + index)
        attnum := UInt16.ofNat (index + 1)
      } }

private def changeName (actual : Array Pg.Protocol.ColumnDesc) (index : Nat)
    (name : String) : Array Pg.Protocol.ColumnDesc :=
  actual.set! index { actual[index]! with name }

private def changeTypeOid (actual : Array Pg.Protocol.ColumnDesc) (index : Nat) :
    Array Pg.Protocol.ColumnDesc :=
  actual.set! index { actual[index]! with typeOid := 4294967295 }

private def changeTypeMod (actual : Array Pg.Protocol.ColumnDesc) (index : Nat) :
    Array Pg.Protocol.ColumnDesc :=
  actual.set! index { actual[index]! with typeMod := 12345 }

private def changeOrigin (actual : Array Pg.Protocol.ColumnDesc) (index : Nat) :
    Array Pg.Protocol.ColumnDesc :=
  actual.set! index { actual[index]! with tableOid := 4294967295 }

private def changeAttnum (actual : Array Pg.Protocol.ColumnDesc) (index : Nat) :
    Array Pg.Protocol.ColumnDesc :=
  actual.set! index { actual[index]! with attnum := 65535 }

private def changeFormat (actual : Array Pg.Protocol.ColumnDesc) (index : Nat) :
    Array Pg.Protocol.ColumnDesc :=
  let column := actual[index]!
  actual.set! index { column with format := if column.format == 0 then 1 else 0 }

private structure SemanticCase where
  label : String
  expectedColumns : Array PreparedColumnPlan
  actualColumns : Array Pg.Protocol.ColumnDesc
  checkFormat : Bool
  expectedResult : Except Error Unit

private def validCase (label : String) (count : Nat) (checkFormat : Bool) :
    SemanticCase :=
  let expected := expectedColumns count
  { label, expectedColumns := expected, actualColumns := actualColumns expected,
    checkFormat, expectedResult := .ok () }

private def driftCase (label : String) (expected : Array PreparedColumnPlan)
    (actual : Array Pg.Protocol.ColumnDesc) (checkFormat : Bool)
    (message : String) : SemanticCase :=
  { label, expectedColumns := expected, actualColumns := actual, checkFormat,
    expectedResult := .error (.queryDrift message) }

private def semanticCases : Array SemanticCase := Id.run do
  let mut cases : Array SemanticCase := #[]
  cases := cases.push (validCase "valid-zero-check-format" 0 true)
  cases := cases.push (validCase "valid-zero-ignore-format" 0 false)
  cases := cases.push (validCase "valid-one-check-format" 1 true)
  cases := cases.push (validCase "valid-one-ignore-format" 1 false)
  cases := cases.push (validCase "valid-six-check-format" 6 true)
  cases := cases.push (validCase "valid-six-ignore-format" 6 false)

  let one := expectedColumns 1
  let oneActual := actualColumns one
  cases := cases.push (driftCase "size-smaller" one #[] true
    "result column count changed from 1 to 0")
  let two := expectedColumns 2
  cases := cases.push (driftCase "size-larger" one (actualColumns two) true
    "result column count changed from 1 to 2")

  let six := expectedColumns 6
  let sixActual := actualColumns six
  let positions : Array (Nat × String) := #[(0, "first"), (3, "middle"), (5, "last")]
  for (index, position) in positions do
    let want := six[index]!
    let renamed := s!"renamed_{position}"
    cases := cases.push (driftCase s!"name-{position}" six
      (changeName sixActual index renamed) true
      s!"result column {index + 1} changed name from {want.name} to {renamed}")
    cases := cases.push (driftCase s!"type-oid-{position}" six
      (changeTypeOid sixActual index) true
      s!"result column {want.name} changed PostgreSQL type")
    cases := cases.push (driftCase s!"type-mod-{position}" six
      (changeTypeMod sixActual index) true
      s!"result column {want.name} changed type modifier")
    cases := cases.push (driftCase s!"format-{position}" six
      (changeFormat sixActual index) true
      s!"result column {want.name} changed wire format")

  let sixOrigins := expectedColumnsWithOrigins 6
  let sixOriginsActual := actualColumns sixOrigins
  for (index, position) in positions do
    let want := sixOrigins[index]!
    cases := cases.push (driftCase s!"origin-table-{position}" sixOrigins
      (changeOrigin sixOriginsActual index) true
      s!"result column {want.name} changed symbolic origin")
    cases := cases.push (driftCase s!"origin-attnum-{position}" sixOrigins
      (changeAttnum sixOriginsActual index) true
      s!"result column {want.name} changed symbolic origin")

  cases := cases.push {
    label := "format-ignored"
    expectedColumns := one
    actualColumns := changeFormat oneActual 0
    checkFormat := false
    expectedResult := .ok ()
  }

  let noneExpected : Array PreparedColumnPlan := #[{ expectedColumn 1 with origin := none }]
  let noneActual := actualColumns noneExpected
  cases := cases.push {
    label := "origin-none-ignored"
    expectedColumns := noneExpected
    actualColumns := noneActual.set! 0 {
      noneActual[0]! with tableOid := 4294967295, attnum := 65535 }
    checkFormat := true
    expectedResult := .ok ()
  }
  cases := cases.push {
    label := "type-size-ignored"
    expectedColumns := one
    actualColumns := oneActual.set! 0 { oneActual[0]! with typeSize := 32767 }
    checkFormat := true
    expectedResult := .ok ()
  }

  let precedenceExpected := expectedColumnsWithOrigins 1
  let precedenceActual := actualColumns precedenceExpected
  let nameFirst := precedenceActual
    |> (fun values => changeFormat values 0)
    |> (fun values => changeOrigin values 0)
    |> (fun values => changeTypeMod values 0)
    |> (fun values => changeTypeOid values 0)
    |> (fun values => changeName values 0 "first")
  cases := cases.push (driftCase "field-precedence-name"
    precedenceExpected nameFirst true
    "result column 1 changed name from column_1 to first")
  let typeOidFirst := precedenceActual
    |> (fun values => changeFormat values 0)
    |> (fun values => changeOrigin values 0)
    |> (fun values => changeTypeMod values 0)
    |> (fun values => changeTypeOid values 0)
  cases := cases.push (driftCase "field-precedence-type-oid"
    precedenceExpected typeOidFirst true
    "result column column_1 changed PostgreSQL type")
  let typeModFirst := precedenceActual
    |> (fun values => changeFormat values 0)
    |> (fun values => changeOrigin values 0)
    |> (fun values => changeTypeMod values 0)
  cases := cases.push (driftCase "field-precedence-type-mod"
    precedenceExpected typeModFirst true
    "result column column_1 changed type modifier")
  let originFirst := precedenceActual
    |> (fun values => changeFormat values 0)
    |> (fun values => changeOrigin values 0)
  cases := cases.push (driftCase "field-precedence-origin"
    precedenceExpected originFirst true
    "result column column_1 changed symbolic origin")

  let twoOrigins := expectedColumnsWithOrigins 2
  let twoOriginsActual := actualColumns twoOrigins
  let leftmostFirst := twoOriginsActual
    |> (fun values => changeFormat values 0)
    |> (fun values => changeName values 1 "earlier-field-later-column")
  cases := cases.push (driftCase "column-precedence-leftmost" twoOrigins
    leftmostFirst true "result column column_1 changed wire format")
  let ignoredThenSecond := twoOriginsActual
    |> (fun values => changeFormat values 0)
    |> (fun values => changeName values 1 "second-renamed")
  cases := cases.push (driftCase "format-disabled-then-next-column" twoOrigins
    ignoredThenSecond false
    "result column 2 changed name from column_2 to second-renamed")
  return cases

private def exactResultEq : Except Error Unit → Except Error Unit → Bool
  | .ok (), .ok () => true
  | .error left, .error right =>
    left.kind == right.kind && left.toMessage == right.toMessage
  | _, _ => false

private def validateSemantics : IO Nat := do
  for fixture in semanticCases do
    let reference := verifyReference fixture.expectedColumns fixture.actualColumns
      fixture.checkFormat
    let candidate := verifyCandidate fixture.expectedColumns fixture.actualColumns
      fixture.checkFormat
    unless exactResultEq reference fixture.expectedResult do
      throw (IO.userError s!"{fixture.label}: reference differs from expected")
    unless exactResultEq candidate fixture.expectedResult do
      throw (IO.userError s!"{fixture.label}: candidate differs from expected")
    unless exactResultEq reference candidate do
      throw (IO.userError s!"{fixture.label}: reference and candidate differ")
  pure semanticCases.size

@[inline] private def mix (digest value : UInt64) : UInt64 :=
  (digest ^^^ value) * 1099511628211

@[inline] private def digestString (digest : UInt64) (value : @& String) : UInt64 := Id.run do
  let mut digest := mix digest (UInt64.ofNat value.toUTF8.size)
  for byte in value.toUTF8 do
    digest := mix digest (UInt64.ofNat byte.toNat + 1)
  return digest

@[noinline] private def descriptorDigest (expected : @& Array PreparedColumnPlan)
    (actual : @& Array Pg.Protocol.ColumnDesc) (checkFormat : Bool) : UInt64 := Id.run do
  let mut digest := mix 1469598103934665603 (UInt64.ofNat expected.size)
  for column in expected do
    digest := digestString digest column.name
    digest := mix digest (UInt64.ofNat column.typeOid.toNat)
    digest := mix digest (UInt64.ofNat column.typeMod.toUInt32.toNat)
    match column.origin with
    | none => digest := mix digest 0
    | some origin =>
      digest := mix digest 1
      digest := mix digest (UInt64.ofNat origin.tableOid.toNat)
      digest := mix digest (UInt64.ofNat origin.attnum.toNat)
    digest := mix digest (UInt64.ofNat column.format.toNat)
  digest := mix digest (UInt64.ofNat actual.size)
  for column in actual do
    digest := digestString digest column.name
    digest := mix digest (UInt64.ofNat column.tableOid.toNat)
    digest := mix digest (UInt64.ofNat column.attnum.toNat)
    digest := mix digest (UInt64.ofNat column.typeOid.toNat)
    digest := mix digest (UInt64.ofNat column.typeSize.toUInt16.toNat)
    digest := mix digest (UInt64.ofNat column.typeMod.toUInt32.toNat)
    digest := mix digest (UInt64.ofNat column.format.toNat)
  return mix digest (if checkFormat then 1 else 0)

@[noinline] private def freshExpected (value : @& Array PreparedColumnPlan) :
    Array PreparedColumnPlan :=
  value

@[noinline] private def freshActual (value : @& Array Pg.Protocol.ColumnDesc) :
    Array Pg.Protocol.ColumnDesc :=
  value

@[noinline] private def runReference (expected : @& Array PreparedColumnPlan)
    (actual : @& Array Pg.Protocol.ColumnDesc) (checkFormat : Bool)
    (digest : UInt64) (iterations : Nat) : Except Error UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    verifyReference (freshExpected expected) (freshActual actual) checkFormat
    checksum := checksum + digest
  pure checksum

@[noinline] private def runCandidate (expected : @& Array PreparedColumnPlan)
    (actual : @& Array Pg.Protocol.ColumnDesc) (checkFormat : Bool)
    (digest : UInt64) (iterations : Nat) : Except Error UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    verifyCandidate (freshExpected expected) (freshActual actual) checkFormat
    checksum := checksum + digest
  pure checksum

private inductive Mode where
  | reference
  | candidate

private def runIterations (mode : Mode) (expected : @& Array PreparedColumnPlan)
    (actual : @& Array Pg.Protocol.ColumnDesc) (checkFormat : Bool)
    (digest : UInt64) (iterations : Nat) : Except Error UInt64 :=
  match mode with
  | .reference => runReference expected actual checkFormat digest iterations
  | .candidate => runCandidate expected actual checkFormat digest iterations

private def parseNatural (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a nonnegative decimal integer")
  pure parsed

private def parseBool (value : String) : IO Bool :=
  match value with
  | "true" => pure true
  | "false" => pure false
  | _ => throw (IO.userError "checkFormat must be true or false")

private def supportedCount (count : Nat) : Bool :=
  count == 0 || count == 1 || count == 6

def runMain (args : List String) : IO Unit := do
  let (modeName, count, checkFormat, iterations, warmup) ← match args with
    | [mode, count, checkFormat, iterations, warmup] =>
      pure (mode,
        ← parseNatural "count" count,
        ← parseBool checkFormat,
        ← parseNatural "iterations" iterations,
        ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: prepared_column_verification_benchmark (reference|candidate) " ++
          "(0|1|6) (true|false) iterations warmup")
  let mode ← match modeName with
    | "reference" => pure Mode.reference
    | "candidate" => pure Mode.candidate
    | _ => throw (IO.userError "mode must be reference or candidate")
  unless supportedCount count do
    throw (IO.userError s!"unsupported result count {count}; expected 0, 1, or 6")

  let cases ← validateSemantics
  let expected := expectedColumns count
  let actual := actualColumns expected
  let digest := descriptorDigest expected actual checkFormat
  unless digest != 0 do
    throw (IO.userError "selected descriptor digest is zero")
  let warmupChecksum ← match runIterations mode expected actual checkFormat digest warmup with
    | .ok checksum => pure checksum
    | .error error => throw (IO.userError error.toMessage)
  unless warmupChecksum == digest * UInt64.ofNat warmup do
    throw (IO.userError "warmup checksum mismatch")
  let checksum ← match runIterations mode expected actual checkFormat digest iterations with
    | .ok checksum => pure checksum
    | .error error => throw (IO.userError error.toMessage)
  unless checksum == digest * UInt64.ofNat iterations do
    throw (IO.userError "measured checksum mismatch")
  IO.println <| s!"benchmark=pgx_prepared_column_verification_v1 mode={modeName} " ++
    s!"count={count} check_format={checkFormat} iterations={iterations} " ++
    s!"warmup={warmup} checksum={checksum}"
  IO.println <| s!"prepared_column_verification_validation=pass cases={cases} " ++
    "result=exact reference=candidate expected=pass"

end Pgx.Typed.PreparedColumnVerificationBenchmarkHarness

def main (args : List String) : IO Unit :=
  Pgx.Typed.PreparedColumnVerificationBenchmarkHarness.runMain args
