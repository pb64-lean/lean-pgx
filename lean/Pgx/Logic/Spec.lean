module

public import Pgx.Logic.State
public import Pgx.Constraint.IR

public section

/-!
# State-transition specifications

These declarations are deliberately independent of a concrete database
runner.  They describe logical pre/postconditions and when relational
obligations must hold, without treating an external PostgreSQL response as a
proof.
-/

namespace Pgx.Logic

/-- PostgreSQL checks non-deferrable obligations at statement completion and
deferrable obligations no later than transaction completion. -/
inductive ObligationTiming where
  | statementEnd
  | transactionEnd
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Static lifecycle facts recovered from `pg_constraint`.  They describe
when a whole-state relational proposition may be required; they do not assert
that the proposition holds for an external database. -/
structure ConstraintLifecycle where
  enforced : Bool := true
  validated : Bool := true
  deferrable : Bool := false
  initiallyDeferred : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ConstraintLifecycle

/-- PostgreSQL's default checking point before any transaction-local
`SET CONSTRAINTS` override. -/
def defaultTiming (lifecycle : ConstraintLifecycle) : ObligationTiming :=
  if lifecycle.deferrable && lifecycle.initiallyDeferred then
    .transactionEnd
  else
    .statementEnd

/-- Phases at which generated whole-state integrity contexts are useful.
`defaultStatementEnd` deliberately means the catalog's default timing; a
transaction which changes a deferrable constraint's mode must select its own
obligations explicitly. -/
inductive Phase where
  | existingSnapshot
  | defaultStatementEnd
  | transactionEnd
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether a supported constraint contributes a whole-state proposition at
the selected phase.  `NOT VALID` constraints are excluded because PostgreSQL
does not promise that pre-existing rows satisfy them. -/
def requiresWholeState (lifecycle : ConstraintLifecycle) : Phase → Bool
  | .existingSnapshot => lifecycle.enforced && lifecycle.validated
  | .defaultStatementEnd =>
      lifecycle.enforced && lifecycle.validated &&
        lifecycle.defaultTiming == .statementEnd
  | .transactionEnd => lifecycle.enforced && lifecycle.validated

end ConstraintLifecycle

/-- The primitive mutation classes used by generated transition metadata. -/
inductive MutationKind where
  | insert
  | delete
  | update
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A relational obligation attached to a mutation and a checking point. -/
structure MutationObligation (schema : Schema) where
  mutation : MutationKind
  timing : ObligationTiming
  condition : State schema → State schema → Prop

namespace MutationObligation

def Holds (obligation : MutationObligation schema)
    (before after : State schema) : Prop :=
  obligation.condition before after

end MutationObligation

/-- A SQL-valued state check.  It reuses the local-constraint truth type and
its PostgreSQL `CHECK` acceptance rule: only `false` violates the obligation. -/
structure SqlStateObligation (schema : Schema) where
  timing : ObligationTiming
  evaluate : State schema → Pgx.Constraint.SqlTruth

namespace SqlStateObligation

def Holds (obligation : SqlStateObligation schema) (state : State schema) : Prop :=
  (obligation.evaluate state).checkPasses

instance (obligation : SqlStateObligation schema) (state : State schema) :
    Decidable (obligation.Holds state) :=
  inferInstanceAs (Decidable (obligation.evaluate state).checkPasses)

end SqlStateObligation

/-- Hoare-style specification of a database operation. -/
structure DbSpec (schema : Schema) (result : Type) where
  pre : State schema → Prop
  post : State schema → result → State schema → Prop

namespace DbSpec

def Accepts (spec : DbSpec schema result) (before : State schema)
    (value : result) (after : State schema) : Prop :=
  spec.pre before ∧ spec.post before value after

/-- Specification of a pure result which leaves the logical state unchanged. -/
def pure (value : result) : DbSpec schema result where
  pre := fun _ => True
  post := fun before actual after => actual = value ∧ after = before

/-- Specification of a deterministic state transition. -/
def transition (step : State schema → State schema) : DbSpec schema Unit where
  pre := fun _ => True
  post := fun before _ after => after = step before

/-- Insert one logical occurrence and require an explicit post-state
integrity predicate. -/
def insert (table : schema.Table) (row : schema.Row table)
    (integrity : State schema → Prop) : DbSpec schema Unit where
  pre := fun _ => True
  post := fun before _ after =>
    after = before.insert table row ∧ integrity after

/-- Delete one identified occurrence from a fixed pre-state.  Fixing the
state keeps occurrence identity well-typed and makes the specification
independent of any live PostgreSQL row identifier. -/
def deleteOccurrence (before : State schema) (table : schema.Table)
    (occurrence : OccAt before table) (integrity : State schema → Prop) :
    DbSpec schema Unit where
  pre := fun actual => actual = before
  post := fun actual _ after =>
    actual = before ∧
      after = before.deleteOccurrence table occurrence ∧ integrity after

/-- Update one identified occurrence in a fixed pre-state and require the
chosen post-state integrity predicate. -/
def updateOccurrence (before : State schema) (table : schema.Table)
    (occurrence : OccAt before table) (replacement : schema.Row table)
    (integrity : State schema → Prop) : DbSpec schema Unit where
  pre := fun actual => actual = before
  post := fun actual _ after =>
    actual = before ∧
      after = before.updateOccurrence table occurrence replacement ∧ integrity after

end DbSpec

/-- Predicate-transformer presentation used by later transaction runtimes. -/
abbrev DbWP (schema : Schema) (result : Type) :=
  (result → State schema → Prop) → State schema → Prop

end Pgx.Logic
