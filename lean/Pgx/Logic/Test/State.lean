import Pgx.Logic.Spec

namespace Pgx.Logic.Test.State

private inductive Table where
  | users
  | audit
  deriving Repr, BEq, DecidableEq

private abbrev Row : Table → Type
  | .users => Nat
  | .audit => String

private abbrev schema : Pgx.Logic.Schema := {
  Table
  Row
  tableDecidableEq := inferInstance
}

private def initial : Pgx.Logic.State schema where
  rows
    | .users => #[10, 10, 20]
    | .audit => #["created"]

private def firstDuplicate : Pgx.Logic.OccAt initial .users :=
  ⟨⟨0, by decide⟩⟩

private def secondDuplicate : Pgx.Logic.OccAt initial .users :=
  ⟨⟨1, by decide⟩⟩

private theorem duplicate_values_have_distinct_occurrences :
    firstDuplicate.row = secondDuplicate.row ∧
      firstDuplicate.index ≠ secondDuplicate.index := by
  decide

private theorem duplicate_value_is_a_member :
    Pgx.Logic.Mem initial .users 10 := by
  exact ⟨firstDuplicate, rfl⟩

private def reordered : Pgx.Logic.State schema where
  rows
    | .users => #[20, 10, 10]
    | .audit => #["created"]

private theorem reordered_is_bag_equivalent :
    Pgx.Logic.State.Equivalent initial reordered := by
  intro table
  cases table
  · change [10, 10, 20].Perm [20, 10, 10]
    decide
  · exact List.Perm.refl _

private theorem insert_updates_only_the_selected_table :
    let inserted := initial.insert .users 30
    inserted.rows .users = #[10, 10, 20, 30] ∧
      inserted.rows .audit = #["created"] := by
  decide

private theorem delete_removes_one_duplicate_occurrence :
    let deleted := initial.deleteOccurrence .users secondDuplicate
    (deleted.rows .users).size = 2 ∧
      deleted.rows .audit = #["created"] := by
  constructor
  · have size := Array.size_eraseIdx secondDuplicate.index.val
        secondDuplicate.index.isLt
    simpa [Pgx.Logic.State.deleteOccurrence, initial] using size
  · simp [Pgx.Logic.State.deleteOccurrence, initial]

private theorem update_replaces_only_one_occurrence :
    let updated := initial.updateOccurrence .users firstDuplicate 99
    updated.rows .users = #[99, 10, 20] ∧
      updated.rows .audit = #["created"] := by
  decide

private theorem occurrence_enumeration_preserves_duplicates :
    (initial.occurrences .users).size = 3 := by
  decide

private theorem transition_spec_describes_insert :
    let spec := Pgx.Logic.DbSpec.transition
      (fun state : Pgx.Logic.State schema => state.insert .users 30)
    spec.Accepts initial () (initial.insert .users 30) := by
  exact ⟨trivial, rfl⟩

def main : IO Unit := do
  assert! firstDuplicate.row == 10
  assert! secondDuplicate.row == 10
  assert! firstDuplicate.index != secondDuplicate.index
  assert! (initial.insert .users 30).rows .users == #[10, 10, 20, 30]
  assert! (initial.deleteOccurrence .users secondDuplicate).rows .users == #[10, 20]
  assert! (initial.updateOccurrence .users firstDuplicate 99).rows .users == #[99, 10, 20]
  assert! (initial.occurrences .users).size == 3
  IO.println "PASS array-backed relational state kernel"

end Pgx.Logic.Test.State

def main : IO Unit :=
  Pgx.Logic.Test.State.main
