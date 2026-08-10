module

public import Pgx.Constraint.IR
public import Pgx.Typed.Containers
public import Pg.Types.Numeric
public import Pg.Types.Interval

public section

/-!
# Executable local-constraint semantics

The definitions in this module are the small proof-producing runtime used by
generated domain and row refinements.  SQL expression evaluation is explicit
about failure and about PostgreSQL's third truth value.  A generated refined
value is therefore constructed only after its local checks have been evaluated
again in Lean.
-/

namespace Pgx.Constraint

namespace SqlTruth

/-- Embed a nullable SQL Boolean. -/
def ofOptionBool : Option Bool → SqlTruth
  | none => .unknown
  | some Bool.true => .true
  | some Bool.false => .false

def toOptionBool : SqlTruth → Option Bool
  | .true => some Bool.true
  | .false => some Bool.false
  | .unknown => none

/-- SQL `NOT`. -/
def negate : SqlTruth → SqlTruth
  | .true => .false
  | .false => .true
  | .unknown => .unknown

/-- SQL three-valued `AND`. -/
def conjunction : SqlTruth → SqlTruth → SqlTruth
  | .false, _ | _, .false => .false
  | .true, right => right
  | left, .true => left
  | .unknown, .unknown => .unknown

/-- SQL three-valued `OR`. -/
def disjunction : SqlTruth → SqlTruth → SqlTruth
  | .true, _ | _, .true => .true
  | .false, right => right
  | left, .false => left
  | .unknown, .unknown => .unknown

def isNull : Option α → SqlTruth
  | none => .true
  | some _ => .false

def isNotNull : Option α → SqlTruth
  | none => .false
  | some _ => .true

end SqlTruth

/-- A modeled SQL operation can fail (for example, fixed-width integer
arithmetic can overflow) instead of silently acquiring Lean's semantics. -/
inductive EvaluationError where
  | overflow (operation target : String)
  | invalidValue (operation message : String)
  deriving Repr, BEq, Inhabited

namespace EvaluationError

def toMessage : EvaluationError → String
  | .overflow operation target =>
      s!"{operation} overflow while evaluating PostgreSQL {target}"
  | .invalidValue operation message => s!"{operation}: {message}"

end EvaluationError

instance : ToString EvaluationError := ⟨EvaluationError.toMessage⟩

/-- Failure returned by a proof-producing local validator. -/
inductive Violation where
  | checkFailed (constraint : String)
  | evaluationFailed (constraint : String) (error : EvaluationError)
  /-- Defensive fallback.  It is unreachable for `Check` values constructed
  through this module, but retaining a total diagnostic keeps validation
  executable without an axiom or unchecked cast. -/
  | inconsistentValidator
  deriving Repr, BEq, Inhabited

namespace Violation

def toMessage : Violation → String
  | .checkFailed constraint => s!"PostgreSQL check {constraint} evaluated to false"
  | .evaluationFailed constraint error =>
      s!"PostgreSQL check {constraint} could not be evaluated: {error}"
  | .inconsistentValidator => "local constraint validator produced no diagnostic"

end Violation

instance : ToString Violation := ⟨Violation.toMessage⟩

/-- Public name used by generated validator signatures. -/
abbrev ConstraintViolation := Violation

/-- SQL evaluation errors do not prove a local guarantee. -/
@[expose] def resultPasses : Except EvaluationError SqlTruth → Prop
  | .ok truth => truth.checkPasses
  | .error _ => False

instance (result : Except EvaluationError SqlTruth) : Decidable (resultPasses result) :=
  match result with
  | .ok truth => inferInstanceAs (Decidable truth.checkPasses)
  | .error _ => isFalse id

/-- Lift a unary modeled operation through SQL null. -/
def liftNullable (operation : α → Except EvaluationError β) :
    Option α → Except EvaluationError (Option β)
  | none => .ok none
  | some value => some <$> operation value

/-- Lift a binary strict modeled operation through SQL null. -/
def liftNullable₂ (operation : α → β → Except EvaluationError γ) :
    Option α → Option β → Except EvaluationError (Option γ)
  | some left, some right => some <$> operation left right
  | _, _ => .ok none

/-- Apply a scalar type-modifier predicate to every element of a nullable
one-dimensional array.  A null array or null element contributes SQL unknown;
an invalid non-null element still makes the combined result false. -/
def evaluateArrayElements
    (evaluate : Option α → Except EvaluationError SqlTruth)
    (values : Option (Array (Option α))) : Except EvaluationError SqlTruth := do
  let some values := values
    | pure .unknown
  let mut result := SqlTruth.true
  for value in values do
    result := result.conjunction (← evaluate value)
  pure result

/-- PostgreSQL domains declared `NOT NULL` reject null values even when they
occur as elements of an array of that domain. -/
def arrayElementsNotNull (values : Array (Option α)) : SqlTruth :=
  if values.any (fun value => value.isNone) then .false else .true

/-- Apply a scalar refinement to every finite bound of a range.  Infinite
bounds and the distinguished empty range contain no scalar value to check. -/
def evaluateRangeBounds
    (evaluate : Option α → Except EvaluationError SqlTruth) :
    Pgx.Typed.PgRange α → Except EvaluationError SqlTruth
  | .empty => pure .true
  | .span lower upper => do
      let lowerTruth ← match lower with
        | none => pure .true
        | some bound => evaluate (some bound.value)
      let upperTruth ← match upper with
        | none => pure .true
        | some bound => evaluate (some bound.value)
      pure (lowerTruth.conjunction upperTruth)

/-- Apply a scalar refinement to all finite bounds of every range in a
multirange. -/
def evaluateMultirangeBounds
    (evaluate : Option α → Except EvaluationError SqlTruth)
    (values : Pgx.Typed.PgMultirange α) : Except EvaluationError SqlTruth := do
  let mut result := SqlTruth.true
  for value in values do
    result := result.conjunction (← evaluateRangeBounds evaluate value)
  pure result

def equalNullable [BEq α] (left right : Option α) : SqlTruth :=
  match left, right with
  | some left, some right => SqlTruth.ofOptionBool (some (left == right))
  | _, _ => .unknown

def notEqualNullable [BEq α] (left right : Option α) : SqlTruth :=
  (equalNullable left right).negate

private def orderingHolds (operator : Comparison) : Ordering → Bool
  | .lt => operator == .lt || operator == .le || operator == .ne
  | .eq => operator == .eq || operator == .le || operator == .ge
  | .gt => operator == .gt || operator == .ge || operator == .ne

/-- Compare non-collated, totally ordered exact scalar values.  Generators
must reject SQL orderings whose PostgreSQL semantics are not represented by
the supplied Lean `Ord` instance. -/
def compareNullable [Ord α] (operator : Comparison)
    (left right : Option α) : SqlTruth :=
  match left, right with
  | some left, some right =>
      SqlTruth.ofOptionBool (some (orderingHolds operator (compare left right)))
  | _, _ => .unknown

/-! The string operations below model the deterministic, collation-free
forms admitted by the constraint parser.  PostgreSQL's one-argument `btrim`
removes U+0020 space characters, and `POSITION` counts characters from one
while returning zero when the substring is absent. -/

def charLength (value : String) : Int :=
  Int.ofNat value.length

def btrim (value : String) : String :=
  let left := value.toList.dropWhile (fun char => char == ' ')
  let both := left.reverse.dropWhile (fun char => char == ' ') |>.reverse
  String.ofList both

private def positionChars (needle : List Char) : List Char → Nat → Nat
  | [], _ => 0
  | haystack@(_ :: rest), index =>
      if needle.isPrefixOf haystack then index
      else positionChars needle rest (index + 1)

def position (needle haystack : String) : Int :=
  if needle.isEmpty then 1
  else Int.ofNat (positionChars needle.toList haystack.toList 1)

/-! ## Character type modifiers

PostgreSQL stores `varchar(n)` and `bpchar(n)` type modifiers as `n + 4`.
The distinguished raw value `-1` means unbounded.  Canonical `TypeRef` values
normally represent that value as `none`, but accepting both forms keeps this
helper useful at the wire/catalog boundary as well as during emission.
-/

/-- Decode a raw PostgreSQL `varchar`/`bpchar` type modifier. -/
def decodeRawCharacterTypmod (typmod : Int32) :
    Except EvaluationError (Option Nat) :=
  if typmod == -1 then
    .ok none
  else
    let raw := typmod.toInt
    if raw ≤ 4 then
      .error (.invalidValue "character typmod"
        s!"expected -1 or a stored typmod of at least 5, got {raw}")
    else
      .ok (some (raw - 4).toNat)

/-- Decode the canonical optional type modifier carried by `Pgx.TypeRef`. -/
def decodeCharacterTypmod : Option Int32 → Except EvaluationError (Option Nat)
  | none => .ok none
  | some typmod => decodeRawCharacterTypmod typmod

/-- Evaluate the local proposition induced by a decoded character limit.
Null produces SQL unknown, while an unbounded non-null value always passes.
`String.length` counts Unicode scalar values rather than UTF-8 bytes. -/
def characterLengthBound (limit : Option Nat) : Option String → SqlTruth
  | none => .unknown
  | some value =>
      match limit with
      | none => .true
      | some maximum => if value.length ≤ maximum then .true else .false

/-- Decode and evaluate a `varchar`/`bpchar` type-modifier refinement. -/
def evaluateCharacterTypmod (typmod : Option Int32) (value : Option String) :
    Except EvaluationError SqlTruth := do
  pure (characterLengthBound (← decodeCharacterTypmod typmod) value)

/-! ## Exact numeric type modifiers

PostgreSQL packs `numeric(precision, scale)` into the type modifier after a
four-byte varlena offset.  Precision occupies the upper sixteen bits and
scale is an eleven-bit two's-complement integer.  PostgreSQL 18 accepts
precision `1..1000` and scale `-1000..1000`.

The predicate below recognizes values which already have the declared scale;
it deliberately does not model PostgreSQL's coercive rounding.  Consequently
a value accepted here can be sent without losing information, while a value
which would need server-side rounding is rejected locally.
-/

structure NumericTypmod where
  precision : Nat
  scale : Int
  deriving Repr, BEq, Inhabited

/-- Decode PostgreSQL's catalog/wire representation of a numeric typmod. -/
def decodeRawNumericTypmod (typmod : Int32) :
    Except EvaluationError (Option NumericTypmod) :=
  if typmod == -1 then
    .ok none
  else
    let raw := typmod.toInt
    if raw < 4 then
      .error (.invalidValue "numeric typmod"
        s!"expected -1 or a stored typmod of at least 4, got {raw}")
    else
      let packed := raw - 4
      let precision := ((packed / 65536) % 65536).toNat
      let encodedScale := packed % 2048
      let scale := if encodedScale ≥ 1024 then encodedScale - 2048 else encodedScale
      if precision = 0 ∨ precision > 1000 then
        .error (.invalidValue "numeric typmod"
          s!"precision must be between 1 and 1000, got {precision}")
      else if scale < -1000 ∨ scale > 1000 then
        .error (.invalidValue "numeric typmod"
          s!"scale must be between -1000 and 1000, got {scale}")
      else
        .ok (some { precision, scale })

/-- Decode the canonical optional type modifier carried by `Pgx.TypeRef`. -/
def decodeNumericTypmod : Option Int32 →
    Except EvaluationError (Option NumericTypmod)
  | none => .ok none
  | some typmod => decodeRawNumericTypmod typmod

private structure DecimalExtents where
  /-- Exponent of the highest nonzero base-ten digit (`ones = 0`). -/
  highest : Int
  /-- Exponent of the lowest nonzero base-ten digit (`tenths = -1`). -/
  lowest : Int

private def highestDigitOffset (digit : Nat) : Int :=
  if digit ≥ 1000 then 3
  else if digit ≥ 100 then 2
  else if digit ≥ 10 then 1
  else 0

private def lowestDigitOffset (digit : Nat) : Int :=
  if digit % 10 != 0 then 0
  else if digit % 100 != 0 then 1
  else if digit % 1000 != 0 then 2
  else 3

/-- Locate the nonzero decimal digits without converting through a bounded
integer or floating-point representation. -/
private def numericDecimalExtents (groupWeight : Int) :
    List UInt16 → Except EvaluationError (Option DecimalExtents)
  | [] => .ok none
  | digit :: rest => do
      let raw := digit.toNat
      if raw ≥ 10000 then
        throw (.invalidValue "numeric value"
          s!"base-10000 digit is out of range: {raw}")
      let tail ← numericDecimalExtents (groupWeight - 1) rest
      if raw = 0 then
        pure tail
      else
        let base := 4 * groupWeight
        let current : DecimalExtents := {
          highest := base + highestDigitOffset raw
          lowest := base + lowestDigitOffset raw
        }
        match tail with
        | none => pure (some current)
        | some following => pure (some {
            highest := max current.highest following.highest
            lowest := min current.lowest following.lowest
          })

private def finiteNumericFits (modifier : NumericTypmod)
    (value : Pg.PgNumeric) : Except EvaluationError Bool := do
  let extents ← numericDecimalExtents value.weight value.digits.toList
  match extents with
  | none => pure true
  | some extents =>
      -- A forged `PgNumeric` must not hide physical fractional digits behind
      -- a smaller display scale: its text encoder would otherwise lose them.
      if extents.lowest < -(Int.ofNat value.dscale) then
        throw (.invalidValue "numeric value"
          "display scale hides nonzero fractional digits")
      let maximumWeight := Int.ofNat modifier.precision - modifier.scale
      pure (extents.highest < maximumWeight ∧
        extents.lowest ≥ -modifier.scale)

/-- Evaluate a decoded numeric precision/scale bound.  SQL null is unknown.
For a constrained numeric, PostgreSQL accepts NaN but rejects either infinity;
the same distinction is made here. -/
def numericPrecisionScaleBound (modifier : Option NumericTypmod) :
    Option Pg.PgNumeric → Except EvaluationError SqlTruth
  | none => .ok .unknown
  | some value =>
      match modifier, value.special with
      | none, _ => .ok .true
      | some _, some .nan => .ok .true
      | some _, some .posInf | some _, some .negInf => .ok .false
      | some modifier, none => do
          pure (if ← finiteNumericFits modifier value then .true else .false)

/-- Decode and evaluate a `numeric(precision, scale)` refinement. -/
def evaluateNumericTypmod (typmod : Option Int32) (value : Option Pg.PgNumeric) :
    Except EvaluationError SqlTruth := do
  numericPrecisionScaleBound (← decodeNumericTypmod typmod) value

/-- Compatibility diagnostic for callers which have not yet adopted the
executable numeric refinement. -/
def unsupportedNumericTypmod (typmod : Option Int32) : EvaluationError :=
  .invalidValue "numeric typmod"
    s!"local numeric precision/scale propositions are unsupported ({repr typmod})"

/-! ## Temporal precision type modifiers

`time`, `timestamp`, and `timestamptz` store their modifier directly as a
fractional-second precision from zero through six.  Lean's temporal values
carry nanoseconds, whereas PostgreSQL stores microseconds, so even an
unmodified value must be aligned to 1000 nanoseconds.  `interval` stores its
precision in the low sixteen bits of a packed range/precision modifier and
its time field is already measured in microseconds.
-/

/-- Decode the raw modifier shared by `time`, `timestamp`, and `timestamptz`. -/
def decodeRawTemporalPrecisionTypmod (typmod : Int32) :
    Except EvaluationError (Option Nat) :=
  if typmod == -1 then
    .ok none
  else
    let raw := typmod.toInt
    if raw < 0 ∨ raw > 6 then
      .error (.invalidValue "temporal typmod"
        s!"fractional-second precision must be between 0 and 6, got {raw}")
    else
      .ok (some raw.toNat)

def decodeTemporalPrecisionTypmod : Option Int32 →
    Except EvaluationError (Option Nat)
  | none => .ok none
  | some typmod => decodeRawTemporalPrecisionTypmod typmod

/-- Decode the precision component of PostgreSQL's packed interval typmod.
`0xffff` denotes full/default precision; the upper bits contain its field
range and do not affect this precision predicate. -/
def decodeRawIntervalPrecisionTypmod (typmod : Int32) :
    Except EvaluationError (Option Nat) :=
  if typmod == -1 then
    .ok none
  else
    let raw := typmod.toInt
    if raw < 0 then
      .error (.invalidValue "interval typmod"
        s!"expected -1 or a nonnegative packed typmod, got {raw}")
    else
      let precision := raw % 65536
      if precision = 65535 then
        .ok none
      else if precision > 6 then
        .error (.invalidValue "interval typmod"
          s!"fractional-second precision must be between 0 and 6, got {precision}")
      else
        .ok (some precision.toNat)

def decodeIntervalPrecisionTypmod : Option Int32 →
    Except EvaluationError (Option Nat)
  | none => .ok none
  | some typmod => decodeRawIntervalPrecisionTypmod typmod

private def tenPower : Nat → Nat
  | 0 => 1
  | exponent + 1 => 10 * tenPower exponent

/-- Check a nanosecond field against PostgreSQL's effective temporal
precision.  An absent modifier means PostgreSQL's maximum precision of six. -/
def temporalNanosecondPrecisionBound (precision : Option Nat) :
    Option Int → SqlTruth
  | none => .unknown
  | some nanoseconds =>
      let effective := precision.getD 6
      if effective > 6 then
        .false
      else
        let quantum := Int.ofNat (tenPower (9 - effective))
        if nanoseconds % quantum = 0 then .true else .false

/-- Check an interval's microsecond field against its fractional precision. -/
def intervalMicrosecondPrecisionBound (precision : Option Nat) :
    Option Int → SqlTruth
  | none => .unknown
  | some microseconds =>
      let effective := precision.getD 6
      if effective > 6 then
        .false
      else
        let quantum := Int.ofNat (tenPower (6 - effective))
        if microseconds % quantum = 0 then .true else .false

def evaluateTemporalPrecisionTypmod (typmod : Option Int32)
    (nanoseconds : Option Int) : Except EvaluationError SqlTruth := do
  pure (temporalNanosecondPrecisionBound
    (← decodeTemporalPrecisionTypmod typmod) nanoseconds)

/-- `time` specialization; `nanoseconds` is the value's nanosecond field. -/
def evaluateTimeTypmod := evaluateTemporalPrecisionTypmod

/-- `timestamp` specialization; `nanoseconds` is the value's epoch-relative
nanosecond field. -/
def evaluateTimestampTypmod := evaluateTemporalPrecisionTypmod

/-- `timestamptz` specialization; `nanoseconds` is the value's UTC
epoch-relative nanosecond field. -/
def evaluateTimestamptzTypmod := evaluateTemporalPrecisionTypmod

def evaluateIntervalPrecisionTypmod (typmod : Option Int32)
    (microseconds : Option Int) : Except EvaluationError SqlTruth := do
  pure (intervalMicrosecondPrecisionBound
    (← decodeIntervalPrecisionTypmod typmod) microseconds)

/-- Apply the interval precision refinement directly to `Pg.PgInterval`. -/
def evaluatePgIntervalPrecisionTypmod (typmod : Option Int32) :
    Option Pg.PgInterval → Except EvaluationError SqlTruth
  | none => .ok .unknown
  | some value => evaluateIntervalPrecisionTypmod typmod (some value.micros)

/-- One independently named PostgreSQL check over a decoded Lean value. -/
structure Check (α : Type u) where
  name : String
  evaluate : α → Except EvaluationError SqlTruth

/-- Every check must either evaluate to true or to SQL unknown. -/
@[expose] def Valid : List (Check α) → α → Prop
  | [], _ => True
  | check :: rest, value =>
      resultPasses (check.evaluate value) ∧ Valid rest value

/-- Kept as an explicit structurally recursive program so generated
validators remain executable even when compiler support for proof recursors
is intentionally restricted. -/
def validDecidable :
    (checks : List (Check α)) → (value : α) → Decidable (Valid checks value)
  | [], _ => isTrue trivial
  | check :: rest, value =>
      match inferInstanceAs (Decidable (resultPasses (check.evaluate value))),
          validDecidable rest value with
      | isTrue head, isTrue tail => isTrue ⟨head, tail⟩
      | isFalse head, _ => isFalse (fun valid => head valid.1)
      | _, isFalse tail => isFalse (fun valid => tail valid.2)

instance (checks : List (Check α)) (value : α) : Decidable (Valid checks value) :=
  validDecidable checks value

/-- Return the first failure in deterministic generated-check order. -/
def firstViolation? : List (Check α) → α → Option Violation
  | [], _ => none
  | check :: rest, value =>
      match check.evaluate value with
      | .error error => some (.evaluationFailed check.name error)
      | .ok .false => some (.checkFailed check.name)
      | .ok .true | .ok .unknown => firstViolation? rest value

/-- Construct a proof-bearing value only by executing its local checks. -/
@[expose] def validate (checks : List (Check α)) (value : α) :
    Except Violation { refined : α // Valid checks refined } :=
  if valid : Valid checks value then
    .ok ⟨value, valid⟩
  else
    .error ((firstViolation? checks value).getD .inconsistentValidator)

theorem validate_sound (checks : List (Check α)) {value : α}
    {refined : { candidate : α // Valid checks candidate }} :
    validate checks value = .ok refined →
      refined.val = value ∧ Valid checks value := by
  intro accepted
  simp only [validate] at accepted
  split at accepted
  next valid =>
    have refined_eq : refined = ⟨value, valid⟩ := Except.ok.inj accepted.symm
    subst refined
    exact ⟨rfl, valid⟩
  next _ => contradiction

theorem validate_complete (checks : List (Check α)) {value : α} :
    Valid checks value →
      ∃ refined, validate checks value = .ok refined := by
  intro valid
  exact ⟨⟨value, valid⟩, by simp [validate, valid]⟩

end Pgx.Constraint

namespace Pgx

/-- Public runtime name used by generated proof-producing validators. -/
abbrev ConstraintViolation := Constraint.ConstraintViolation

end Pgx
