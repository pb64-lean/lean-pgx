import Pgx.Constraint.Semantics

namespace Pgx.Test.Typmod

open Pgx.Constraint

private def failed (result : Except EvaluationError α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def okEq [BEq α] (result : Except EvaluationError α)
    (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def numeric (source : String) : Pg.PgNumeric :=
  match Pg.PgNumeric.fromString source with
  | .ok value => value
  | .error _ => default

def main : IO UInt32 := do
  -- PostgreSQL stores varchar(n)/bpchar(n) as n + the four-byte varlena
  -- header.  Both canonical `none` and the raw sentinel -1 are unbounded.
  assert! okEq (decodeRawCharacterTypmod 9) (some 5)
  assert! okEq (decodeRawCharacterTypmod (-1)) (none : Option Nat)
  assert! okEq (decodeCharacterTypmod none) (none : Option Nat)
  assert! okEq (decodeCharacterTypmod (some 68)) (some 64)

  assert! okEq (evaluateCharacterTypmod (some 9) (some "Lean")) .true
  assert! okEq (evaluateCharacterTypmod (some 9) (some "Lean4!")) .false
  assert! okEq (evaluateCharacterTypmod none (some "arbitrarily long")) .true
  assert! okEq (evaluateCharacterTypmod (some 9) none) .unknown

  -- Bounds count characters, not UTF-8 bytes: this value is three Unicode
  -- scalar values despite occupying seven UTF-8 bytes.
  assert! "hé🚀".utf8ByteSize == 7
  assert! okEq (evaluateCharacterTypmod (some 7) (some "hé🚀")) .true
  assert! okEq (evaluateCharacterTypmod (some 6) (some "hé🚀")) .false

  -- Zero-length and negative/non-sentinel raw modifiers cannot be produced
  -- by a valid varchar(n) or bpchar(n) declaration.
  assert! failed (decodeRawCharacterTypmod 4)
  assert! failed (decodeRawCharacterTypmod 0)
  assert! failed (decodeRawCharacterTypmod (-2))
  assert! failed (evaluateCharacterTypmod (some 4) (some ""))

  -- numeric(precision, scale) is packed as
  -- ((precision << 16) | (scale & 0x7ff)) + 4.  The scale is signed.
  assert! okEq (decodeRawNumericTypmod 655366)
    (some { precision := 10, scale := 2 })
  assert! okEq (decodeNumericTypmod none) (none : Option NumericTypmod)
  assert! okEq (decodeRawNumericTypmod (-1)) (none : Option NumericTypmod)
  assert! okEq (decodeRawNumericTypmod 133121)
    (some { precision := 2, scale := -3 })
  assert! okEq (decodeRawNumericTypmod 65537052)
    (some { precision := 1000, scale := -1000 })
  assert! okEq (decodeRawNumericTypmod 65537004)
    (some { precision := 1000, scale := 1000 })

  assert! failed (decodeRawNumericTypmod 4)      -- precision zero
  assert! failed (decodeRawNumericTypmod 3)      -- below varlena offset
  assert! failed (decodeRawNumericTypmod (-2))   -- only -1 is unbounded
  assert! failed (decodeRawNumericTypmod 65601540) -- precision 1001
  assert! failed (decodeRawNumericTypmod 66564)  -- scale -1024
  assert! failed (decodeRawNumericTypmod 66563)  -- scale 1023

  -- Exact values pass numeric(10,2); overflow and values which would need
  -- PostgreSQL's coercive rounding fail locally.
  assert! okEq (evaluateNumericTypmod (some 655366)
    (some (numeric "12345678.90"))) .true
  assert! okEq (evaluateNumericTypmod (some 655366)
    (some (numeric "123456789.01"))) .false
  assert! okEq (evaluateNumericTypmod (some 655366)
    (some (numeric "1.234"))) .false
  assert! okEq (evaluateNumericTypmod (some 655366)
    (some (numeric "1.230"))) .true
  assert! okEq (evaluateNumericTypmod (some 655366) none) .unknown

  -- Scale may exceed precision: numeric(2,4) admits magnitudes below 0.01.
  assert! okEq (evaluateNumericTypmod (some 131080)
    (some (numeric "0.0099"))) .true
  assert! okEq (evaluateNumericTypmod (some 131080)
    (some (numeric "0.0100"))) .false

  -- A negative scale requires trailing integral zeroes.  numeric(2,-3)
  -- permits at most five digits before the decimal point.
  assert! okEq (evaluateNumericTypmod (some 133121)
    (some (numeric "99000"))) .true
  assert! okEq (evaluateNumericTypmod (some 133121)
    (some (numeric "99900"))) .false
  assert! okEq (evaluateNumericTypmod (some 133121)
    (some (numeric "100000"))) .false
  assert! okEq (evaluateNumericTypmod (some 133121)
    (some (numeric "0"))) .true

  -- PostgreSQL permits NaN for every numeric typmod, rejects infinities for
  -- constrained numeric, and permits them when the typmod is unbounded.
  assert! okEq (evaluateNumericTypmod (some 655366)
    (some (numeric "NaN"))) .true
  assert! okEq (evaluateNumericTypmod (some 655366)
    (some (numeric "Infinity"))) .false
  assert! okEq (evaluateNumericTypmod none
    (some (numeric "-Infinity"))) .true

  let invalidDigit : Pg.PgNumeric := { digits := #[10000] }
  assert! failed (evaluateNumericTypmod (some 655366) (some invalidDigit))
  let hiddenFraction : Pg.PgNumeric := {
    digits := #[1], weight := -1, dscale := 0
  }
  assert! failed (evaluateNumericTypmod (some 655366) (some hiddenFraction))

  -- time/timestamp/timestamptz store a direct precision in 0..6.  Lean's
  -- temporal values use nanoseconds, so unmodified values still have to be
  -- aligned to PostgreSQL's microsecond resolution.
  assert! okEq (decodeRawTemporalPrecisionTypmod (-1)) (none : Option Nat)
  assert! okEq (decodeRawTemporalPrecisionTypmod 0) (some 0)
  assert! okEq (decodeRawTemporalPrecisionTypmod 6) (some 6)
  assert! failed (decodeRawTemporalPrecisionTypmod (-2))
  assert! failed (decodeRawTemporalPrecisionTypmod 7)

  assert! okEq (evaluateTimeTypmod (some 3) (some 1234000000)) .true
  assert! okEq (evaluateTimeTypmod (some 3) (some 1234567000)) .false
  assert! okEq (evaluateTimestampTypmod (some 3) (some (-1234000000))) .true
  assert! okEq (evaluateTimestamptzTypmod (some 6) (some 1234567000)) .true
  assert! okEq (evaluateTimestampTypmod none (some 1000)) .true
  assert! okEq (evaluateTimestampTypmod none (some 999)) .false
  assert! okEq (evaluateTimeTypmod (some 0) none) .unknown

  -- Interval range and precision share one Int32.  Full range with precision
  -- three is (0x7fff << 16) | 3; 0xffff means full precision.
  assert! okEq (decodeRawIntervalPrecisionTypmod (-1)) (none : Option Nat)
  assert! okEq (decodeRawIntervalPrecisionTypmod 2147418115) (some 3)
  assert! okEq (decodeRawIntervalPrecisionTypmod 2147483647) (none : Option Nat)
  assert! failed (decodeRawIntervalPrecisionTypmod 2147418119)

  assert! okEq (evaluateIntervalPrecisionTypmod (some 2147418115)
    (some 123000)) .true
  assert! okEq (evaluateIntervalPrecisionTypmod (some 2147418115)
    (some 123456)) .false
  assert! okEq (evaluateIntervalPrecisionTypmod none (some 123456)) .true
  assert! okEq (evaluateIntervalPrecisionTypmod (some 2147418115) none) .unknown
  assert! okEq (evaluatePgIntervalPrecisionTypmod (some 2147418115)
    (some { micros := 123000 })) .true
  return 0

end Pgx.Test.Typmod

def main : IO UInt32 := Pgx.Test.Typmod.main
