import Pgx.Constraint.IR

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
def resultPasses : Except EvaluationError SqlTruth → Prop
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

/-- Numeric precision/scale typmods do not yet have a sound local
proposition.  Code generation can use this stable diagnostic instead of
silently treating them as character-style bounds. -/
def unsupportedNumericTypmod (typmod : Option Int32) : EvaluationError :=
  .invalidValue "numeric typmod"
    s!"local numeric precision/scale propositions are unsupported ({repr typmod})"

/-- One independently named PostgreSQL check over a decoded Lean value. -/
structure Check (α : Type u) where
  name : String
  evaluate : α → Except EvaluationError SqlTruth

/-- Every check must either evaluate to true or to SQL unknown. -/
def Valid : List (Check α) → α → Prop
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
def validate (checks : List (Check α)) (value : α) :
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
