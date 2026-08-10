import Pgx.Logic.Constraint

namespace Pgx.Test.RelationalConstraint

open Pgx.Logic
open Pgx.Logic.Constraint

private inductive Table where
  | items
  | parents
  | children
  deriving Repr, DecidableEq

private abbrev Row (table : Table) : Type :=
  match table with
  | .items => Nat
  | .parents | .children => Unit

private abbrev schema : Schema := {
  Table := Table
  Row := Row
  tableDecidableEq := inferInstance
}

private def state : State schema where
  rows
    | .items => #[0, 1]
    | .parents => #[]
    | .children => #[()]

private def firstItem : OccAt state .items := ⟨⟨0, by decide⟩⟩
private def secondItem : OccAt state .items := ⟨⟨1, by decide⟩⟩
private def onlyChild : OccAt state .children := ⟨⟨0, by decide⟩⟩

private theorem itemsDistinct : DistinctOccurrences firstItem secondItem := by
  simp [DistinctOccurrences, firstItem, secondItem]

private def nullableEqual : Option Nat → Option Nat → SqlTruth
  | some left, some right => if left == right then .true else .false
  | _, _ => .unknown

private def nullableNotDistinct : Option Nat → Option Nat → Bool
  | none, none => true
  | some left, some right => left == right
  | _, _ => false

private def nullableUnique : UniqueComparator (Option Nat) := {
  equal := nullableEqual
  notDistinct := nullableNotDistinct
}

/-! Duplicate null keys do not conflict under ordinary UNIQUE semantics. -/
private theorem duplicateNullsDistinct :
    Unique state .items (fun _ => (none : Option Nat))
      nullableUnique .distinct := by
  intro left right distinct
  rfl

/-! The same duplicate occurrences violate `NULLS NOT DISTINCT`. -/
private theorem duplicateNullsNotDistinct :
    ¬ Unique state .items (fun _ => (none : Option Nat))
      nullableUnique .notDistinct := by
  intro unique
  have conflict := unique firstItem secondItem itemsDistinct
  exact Bool.noConfusion conflict

private def primaryDistinct : PrimaryKeyComparator Nat := {
  allNotNull := fun _ => true
  equal := fun _ _ => .false
}

private def primaryNull : PrimaryKeyComparator Unit := {
  allNotNull := fun _ => false
  equal := fun _ _ => .false
}

private theorem primaryAcceptsNonNullDistinctKeys :
    PrimaryKey state .items (fun occurrence => occurrence)
      primaryDistinct := by
  constructor
  · intro occurrence
    rfl
  · intro left right distinct
    rfl

private theorem primaryRejectsNullKey :
    ¬ PrimaryKey state .items (fun _ => ()) primaryNull := by
  intro primary
  have nonnull := primary.1 firstItem
  exact Bool.noConfusion nonnull

private def partialForeignKey : ForeignKeyComparator Unit Unit := {
  nullShape := fun _ => .partialNulls
  compare := fun _ _ => .false
}

private def allNullForeignKey : ForeignKeyComparator Unit Unit := {
  nullShape := fun _ => .allNulls
  compare := fun _ _ => .false
}

/-! MATCH SIMPLE exempts a key with even one null component. -/
private theorem matchSimpleAcceptsPartialNull :
    ForeignKey state .children .parents .simple (fun _ => ())
      (fun _ => ()) partialForeignKey := by
  intro child
  trivial

/-! MATCH FULL rejects a partially-null compound key, even with no parent. -/
private theorem matchFullRejectsPartialNull :
    ¬ ForeignKey state .children .parents .full (fun _ => ())
      (fun _ => ()) partialForeignKey := by
  intro foreignKey
  have violation := foreignKey onlyChild
  exact violation

/-! MATCH FULL exempts an all-null key. -/
private theorem matchFullAcceptsAllNull :
    ForeignKey state .children .parents .full (fun _ => ())
      (fun _ => ()) allNullForeignKey := by
  intro child
  trivial

private def exclusionUnknown : ExclusionComparator Unit := {
  compare := fun _ _ => #[.true, .unknown]
}

private def exclusionFalse : ExclusionComparator Unit := {
  compare := fun _ _ => #[.true, .false]
}

private def exclusionTrue : ExclusionComparator Unit := {
  compare := fun _ _ => #[.true, .true]
}

private theorem exclusionUnknownNoConflict :
    exclusionUnknown.conflicts () () = false := by
  native_decide

private theorem exclusionFalseNoConflict :
    exclusionFalse.conflicts () () = false := by
  native_decide

private theorem exclusionTrueConflicts :
    exclusionTrue.conflicts () () = true := by
  native_decide

/-! Either unknown or false breaks the all-true exclusion conflict. -/
private theorem exclusionAcceptsUnknown :
    Exclusion state .items (fun _ => ()) exclusionUnknown := by
  intro left right distinct
  exact exclusionUnknownNoConflict

private theorem exclusionAcceptsFalse :
    Exclusion state .items (fun _ => ()) exclusionFalse := by
  intro left right distinct
  exact exclusionFalseNoConflict

/-! Two distinct occurrences violate exclusion when every operator is true. -/
private theorem exclusionRejectsAllTrue :
    ¬ Exclusion state .items (fun _ => ()) exclusionTrue := by
  intro exclusion
  have conflict := exclusion firstItem secondItem itemsDistinct
  rw [exclusionTrueConflicts] at conflict
  exact Bool.noConfusion conflict

def main : IO UInt32 := do
  assert! nullableUnique.conflicts .distinct none none == false
  assert! nullableUnique.conflicts .notDistinct none none == true
  assert! exclusionUnknown.conflicts () () == false
  assert! exclusionFalse.conflicts () () == false
  assert! exclusionTrue.conflicts () () == true
  let _ := duplicateNullsDistinct
  let _ := duplicateNullsNotDistinct
  let _ := primaryAcceptsNonNullDistinctKeys
  let _ := primaryRejectsNullKey
  let _ := matchSimpleAcceptsPartialNull
  let _ := matchFullRejectsPartialNull
  let _ := matchFullAcceptsAllNull
  let _ := exclusionAcceptsUnknown
  let _ := exclusionAcceptsFalse
  let _ := exclusionRejectsAllTrue
  return 0

end Pgx.Test.RelationalConstraint

def main : IO UInt32 := Pgx.Test.RelationalConstraint.main
