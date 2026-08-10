import Pgx.Logic.State
import Pgx.Constraint.IR

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

end DbSpec

/-- Predicate-transformer presentation used by later transaction runtimes. -/
abbrev DbWP (schema : Schema) (result : Type) :=
  (result → State schema → Prop) → State schema → Prop

end Pgx.Logic
