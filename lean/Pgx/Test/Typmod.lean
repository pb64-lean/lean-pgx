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

  let numericError := unsupportedNumericTypmod (some 655366)
  assert! numericError.toMessage.contains "unsupported"
  return 0

end Pgx.Test.Typmod

def main : IO UInt32 := Pgx.Test.Typmod.main
