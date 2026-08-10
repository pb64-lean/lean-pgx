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
