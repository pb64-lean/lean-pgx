import Pgx.Constraint.Semantics

namespace Pgx.Test.ConstraintSemantics

open Pgx.Constraint

private def truthValues : Array SqlTruth := #[.true, .false, .unknown]

private def expectedConjunctions : Array SqlTruth := #[
  .true, .false, .unknown,
  .false, .false, .false,
  .unknown, .false, .unknown
]

private def expectedDisjunctions : Array SqlTruth := #[
  .true, .true, .true,
  .true, .false, .unknown,
  .true, .unknown, .unknown
]

private structure Sample where
  age : Option Int32
  deriving Repr, BEq

private def ageCheck : Check Sample := {
  name := "sample_age_nonnegative"
  evaluate := fun sample =>
    match sample.age with
    | none => .ok .unknown
    | some 99 => .error (.overflow "addition" "int4")
    | some age => .ok (if 0 ≤ age then .true else .false)
}

private def sampleChecks : List (Check Sample) := [ageCheck]

private def Sample.ValidPred (sample : Sample) : Prop :=
  Valid sampleChecks sample

private instance (sample : Sample) : Decidable sample.ValidPred :=
  validDecidable sampleChecks sample

private abbrev RefinedSample := { sample : Sample // sample.ValidPred }

private def validateSample (sample : Sample) :
    Except ConstraintViolation RefinedSample :=
  validate sampleChecks sample

private theorem validateSample_sound {sample : Sample} {refined : RefinedSample} :
    validateSample sample = .ok refined →
      refined.val = sample ∧ sample.ValidPred := by
  exact validate_sound sampleChecks

private theorem validateSample_complete {sample : Sample} :
    sample.ValidPred →
      ∃ refined, validateSample sample = .ok refined := by
  exact validate_complete sampleChecks

private def violation? : Except ConstraintViolation RefinedSample → Option ConstraintViolation
  | .ok _ => none
  | .error violation => some violation

private def checkPassesBool (truth : SqlTruth) : Bool :=
  decide truth.checkPasses

private def uint32Range : IntegerRange Int64 := {
  lower := some { value := 0, inclusive := true }
  upper := some { value := 4294967296, inclusive := false }
}

private def canonicalUInt32Range (value : Option Int64) :
    Except EvaluationError SqlTruth :=
  let scalar := value.map Int64.toInt
  .ok ((compareNullable .ge scalar (some (0 : Int))).conjunction
    (compareNullable .lt scalar (some (4294967296 : Int))))

private def contradictoryRange : IntegerRange Int64 := {
  lower := some { value := 10, inclusive := true }
  upper := some { value := 5, inclusive := false }
}

private def canonicalContradictoryRange (value : Option Int64) :
    Except EvaluationError SqlTruth :=
  let scalar := value.map Int64.toInt
  .ok ((compareNullable .ge scalar (some (10 : Int))).conjunction
    (compareNullable .lt scalar (some (5 : Int))))

private def positiveRange : IntegerRange Int64 := {
  lower := some { value := 0, inclusive := false }
}

/-- Canonical spelling of the reversed SQL comparison `0 < value`. -/
private def canonicalReversedPositive (value : Option Int64) :
    Except EvaluationError SqlTruth :=
  .ok (compareNullable .lt (some (0 : Int)) (value.map Int64.toInt))

private structure DifferentialSample where
  value : Option Int64
  other : Int64
  explode : Bool := false

private def canonicalPositive : Check DifferentialSample := {
  name := "first_positive"
  evaluate := fun sample =>
    .ok (compareNullable .gt (sample.value.map Int64.toInt) (some (0 : Int)))
}

private def canonicalOtherPositive : Check DifferentialSample := {
  name := "second_positive"
  evaluate := fun sample =>
    .ok (compareNullable .gt (some sample.other.toInt) (some (0 : Int)))
}

private def canonicalFallback : Check DifferentialSample := {
  name := "generic_fallback"
  evaluate := fun sample =>
    if sample.explode then .error (.invalidValue "fallback" "fixture")
    else .ok .true
}

private def differentialChecks : List (Check DifferentialSample) :=
  [canonicalPositive, canonicalOtherPositive, canonicalFallback]

private inductive ValidationOutcome where
  | accepted
  | rejected (violation : Violation)
  deriving Repr, BEq

private def canonicalOutcome (sample : DifferentialSample) : ValidationOutcome :=
  match validate differentialChecks sample with
  | .ok _ => .accepted
  | .error violation => .rejected violation

/-- The same source-ordered diagnostic program emitted beside specialized
range predicates. -/
private def specializedOutcome (sample : DifferentialSample) : ValidationOutcome :=
  if positiveRange.HoldsNullable sample.value then
    if positiveRange.HoldsValue sample.other then
      let fallback := canonicalFallback.evaluate sample
      if resultPasses fallback then .accepted
      else .rejected (violationOfResult canonicalFallback.name fallback)
    else .rejected (.checkFailed canonicalOtherPositive.name)
  else .rejected (.checkFailed canonicalPositive.name)

private inductive EvaluationOutcome where
  | ok (truth : SqlTruth)
  | error (failure : EvaluationError)
  deriving Repr, BEq

private def evaluationOutcome : Except EvaluationError SqlTruth → EvaluationOutcome
  | .ok truth => .ok truth
  | .error failure => .error failure

private structure QuantityData where
  quantity : Int64

private def quantityCheck : Check QuantityData := {
  name := "quantity_uint32"
  evaluate := fun value => uint32Range.evaluateValue value.quantity
}

private def quantityChecks : List (Check QuantityData) := [quantityCheck]

@[expose] private def QuantityValid (value : QuantityData) : Prop :=
  Valid quantityChecks value

@[expose] private def QuantitySpecialized (value : QuantityData) : Prop :=
  uint32Range.HoldsValue value.quantity

private theorem quantitySpecialized_iff_valid (value : QuantityData) :
    QuantitySpecialized value ↔ QuantityValid value := by
  simp [QuantitySpecialized, QuantityValid, quantityChecks, quantityCheck,
    Pgx.Constraint.Valid, IntegerRange.resultPasses_evaluateValue_iff]

private abbrev QuantityRow := { value : QuantityData // QuantityValid value }

private theorem quantityFitsUInt32 (value : QuantityRow) :
    Int64FitsUInt32 value.val.quantity := by
  have specialized := (quantitySpecialized_iff_valid value.val).mpr value.property
  simpa [QuantitySpecialized, uint32Range, IntegerRange.HoldsValue,
    IntegerRange.lowerPasses, IntegerRange.upperPasses, Int64FitsUInt32,
    NonnegativeInt64] using specialized

@[inline] private def quantityUInt32 (value : QuantityRow) : UInt32 :=
  uint32OfInt64 value.val.quantity (quantityFitsUInt32 value)

def main : IO UInt32 := do
  let mut index := 0
  for left in truthValues do
    for right in truthValues do
      assert! left.conjunction right == expectedConjunctions[index]!
      assert! left.disjunction right == expectedDisjunctions[index]!
      index := index + 1

  assert! SqlTruth.true.negate == .false
  assert! SqlTruth.false.negate == .true
  assert! SqlTruth.unknown.negate == .unknown

  assert! SqlTruth.isNull (none : Option Int32) == .true
  assert! SqlTruth.isNull (some (1 : Int32)) == .false
  assert! SqlTruth.isNotNull (none : Option Int32) == .false
  assert! SqlTruth.isNotNull (some (1 : Int32)) == .true
  assert! equalNullable (none : Option Int32) (some 1) == .unknown
  assert! equalNullable (some (1 : Int32)) (some 1) == .true
  assert! notEqualNullable (some (1 : Int32)) (some 2) == .true
  assert! compareNullable .lt (some (1 : Int32)) (some 2) == .true
  assert! compareNullable .ge (some (1 : Int32)) (some 2) == .false
  -- Exact Int64 comparison at the first value above UInt32's range.  This is
  -- the representative constant PostgreSQL deparses as
  -- `'4294967296'::bigint` in a BIGINT CHECK.
  let uint32Ceiling : Int64 := 4294967296
  assert! compareNullable .lt (some (4294967295 : Int64)) (some uint32Ceiling) == .true
  assert! compareNullable .lt (some uint32Ceiling) (some uint32Ceiling) == .false
  assert! compareNullable .ge (some uint32Ceiling) (some uint32Ceiling) == .true

  -- The specialized fixed-width evaluator is differential-tested against
  -- the original generic expression shape, not against its own compatibility
  -- `Check`.  Boundaries include SQL null/unknown and the UInt32 ceiling.
  for value in #[none, some (-9223372036854775808), some (-1), some 0,
      some 1, some 4294967295, some 4294967296,
      some 9223372036854775807] do
    assert! evaluationOutcome (uint32Range.evaluateNullable value) ==
      evaluationOutcome (canonicalUInt32Range value)
    assert! decide (uint32Range.HoldsNullable value) ==
      decide (resultPasses (canonicalUInt32Range value))

  -- Reversed literal/column operands normalize to the same range, and even a
  -- contradictory conjunction retains canonical false/unknown behavior.
  for value in #[none, some (-9223372036854775808), some (-1), some 0,
      some 1, some 5, some 10, some 9223372036854775807] do
    assert! evaluationOutcome (positiveRange.evaluateNullable value) ==
      evaluationOutcome (canonicalReversedPositive value)
    assert! evaluationOutcome (contradictoryRange.evaluateNullable value) ==
      evaluationOutcome (canonicalContradictoryRange value)

  -- Exact accept/reject diagnostics agree with canonical `validate`.  The
  -- first fixture has two competing failures plus a later evaluation error;
  -- generated source order must select the first named check.
  for sample in #[
      { value := none, other := 1 },
      { value := some 1, other := 1 },
      { value := some 0, other := 0, explode := true },
      { value := some 1, other := 0, explode := true },
      { value := some 1, other := 1, explode := true }
    ] do
    assert! specializedOutcome sample == canonicalOutcome sample
  assert! specializedOutcome { value := some 0, other := 0, explode := true } ==
    .rejected (.checkFailed "first_positive")
  assert! specializedOutcome { value := some 1, other := 1, explode := true } ==
    .rejected (.evaluationFailed "generic_fallback"
      (.invalidValue "fallback" "fixture"))

  have positiveSeven : PositiveInt64 7 := by
    unfold PositiveInt64
    decide
  have nonnegativeZero : NonnegativeInt64 0 := by
    unfold NonnegativeInt64
    decide
  have maxUInt32 : Int64FitsUInt32 4294967295 := by
    unfold Int64FitsUInt32 NonnegativeInt64
    decide
  assert! uint64OfPositiveInt64 7 positiveSeven == 7
  assert! uint64OfNonnegativeInt64 0 nonnegativeZero == 0
  assert! uint32OfInt64 4294967295 maxUInt32 == (4294967295 : UInt32)
  let quantityRow ← match validate quantityChecks { quantity := 4294967295 } with
    | .ok value => pure value
    | .error violation => throw (IO.userError s!"quantity proof fixture: {violation}")
  assert! quantityUInt32 quantityRow == (4294967295 : UInt32)

  assert! charLength "hé🚀" == 3
  assert! btrim "  hello  " == "hello"
  assert! btrim "\thello\n" == "\thello\n"
  assert! position "@" "a@b.example" == 2
  assert! position "missing" "a@b.example" == 0
  assert! position "" "a@b.example" == 1

  assert! checkPassesBool .true
  assert! !(checkPassesBool .false)
  assert! checkPassesBool .unknown
  assert! decide (resultPasses (.ok .unknown))
  assert! !(decide (resultPasses (.ok .false)))
  assert! !(decide (resultPasses (.error (.invalidValue "test" "failed"))))

  let nullableAccepted := validateSample { age := none }
  let validAccepted := validateSample { age := some 7 }
  assert! nullableAccepted.isOk
  assert! validAccepted.isOk
  assert! violation? (validateSample { age := some (-1) }) ==
    some (.checkFailed "sample_age_nonnegative")
  assert! violation? (validateSample { age := some 99 }) ==
    some (.evaluationFailed "sample_age_nonnegative" (.overflow "addition" "int4"))

  return 0

end Pgx.Test.ConstraintSemantics

def main : IO UInt32 := Pgx.Test.ConstraintSemantics.main
