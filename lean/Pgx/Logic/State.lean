module

public import Pgx.Logic.Schema

public section

/-!
# Finite relational states

Each table is represented by an array of row occurrences.  Array position is
logical occurrence identity only: it preserves duplicate rows without
depending on a PostgreSQL physical identifier such as `ctid`.
-/

namespace Pgx.Logic

universe u v

/-- An immutable, finite, many-sorted database state. -/
structure State (schema : Schema.{u, v}) where
  rows : (table : schema.Table) → Array (schema.Row table)

namespace State

/-- Replace one table while leaving every other table definitionally
unchanged. -/
def setTable (state : State schema) (target : schema.Table)
    (replacement : Array (schema.Row target)) : State schema where
  rows := fun table =>
    if h : table = target then
      h.symm ▸ replacement
    else
      state.rows table

@[simp] theorem rows_setTable_same (state : State schema)
    (table : schema.Table) (replacement : Array (schema.Row table)) :
    (state.setTable table replacement).rows table = replacement := by
  simp [setTable]

@[simp] theorem rows_setTable_other (state : State schema)
    (target table : schema.Table) (replacement : Array (schema.Row target))
    (different : table ≠ target) :
    (state.setTable target replacement).rows table = state.rows table := by
  simp [setTable, different]

/-- Append one new occurrence to a table. -/
def insert (state : State schema) (table : schema.Table)
    (row : schema.Row table) : State schema :=
  state.setTable table ((state.rows table).push row)

@[simp] theorem rows_insert_same (state : State schema)
    (table : schema.Table) (row : schema.Row table) :
    (state.insert table row).rows table = (state.rows table).push row := by
  simp [insert]

@[simp] theorem rows_insert_other (state : State schema)
    (target table : schema.Table) (row : schema.Row target)
    (different : table ≠ target) :
    (state.insert target row).rows table = state.rows table := by
  simp [insert, different]

end State

/-- One occurrence in a table at a particular immutable state.  Two equal
row values at different indices remain distinct occurrences. -/
structure OccAt (state : State schema) (table : schema.Table) where
  index : Fin (state.rows table).size
  deriving DecidableEq

namespace OccAt

/-- The row value carried by an occurrence. -/
def row {schema : Schema} {state : State schema} {table : schema.Table}
    (occurrence : OccAt state table) : schema.Row table :=
  (state.rows table)[occurrence.index]

/-- Occurrence identity is its index in the immutable table bag. -/
def identity {schema : Schema} {state : State schema} {table : schema.Table}
    (occurrence : OccAt state table) :
    Fin (state.rows table).size :=
  occurrence.index

end OccAt

/-- Compatibility spelling for code which treats occurrences as dependent
pairs of a row and a multiplicity witness. -/
def occurrenceValue {schema : Schema} {state : State schema}
    {table : schema.Table} (occurrence : OccAt state table) : schema.Row table :=
  occurrence.row

/-- Positive support of a table bag. -/
def Mem (state : State schema) (table : schema.Table)
    (row : schema.Row table) : Prop :=
  ∃ occurrence : OccAt state table, occurrence.row = row

/-- A row value accompanied by evidence that it occurs at least once. -/
abbrev RowAt (state : State schema) (table : schema.Table) :=
  { row : schema.Row table // Mem state table row }

namespace OccAt

/-- Forget occurrence identity while retaining positive membership. -/
def toRowAt {schema : Schema} {state : State schema} {table : schema.Table}
    (occurrence : OccAt state table) : RowAt state table :=
  ⟨occurrence.row, ⟨occurrence, rfl⟩⟩

end OccAt

namespace State

/-- Enumerate every occurrence exactly once, without requiring a `Fintype`
or Mathlib finite-set dependency. -/
def occurrences (state : State schema) (table : schema.Table) :
    Array (OccAt state table) :=
  Array.ofFn fun index => ⟨index⟩

@[simp] theorem occurrences_size (state : State schema)
    (table : schema.Table) :
    (state.occurrences table).size = (state.rows table).size := by
  simp [occurrences]

/-- Delete exactly the selected occurrence.  Equal rows at other indices are
preserved. -/
def deleteOccurrence (state : State schema) (table : schema.Table)
    (occurrence : OccAt state table) : State schema :=
  state.setTable table <|
    (state.rows table).eraseIdx occurrence.index.val occurrence.index.isLt

@[simp] theorem rows_deleteOccurrence_same (state : State schema)
    (table : schema.Table) (occurrence : OccAt state table) :
    (state.deleteOccurrence table occurrence).rows table =
      (state.rows table).eraseIdx occurrence.index.val occurrence.index.isLt := by
  simp [deleteOccurrence]

@[simp] theorem rows_deleteOccurrence_other (state : State schema)
    (target table : schema.Table) (occurrence : OccAt state target)
    (different : table ≠ target) :
    (state.deleteOccurrence target occurrence).rows table = state.rows table := by
  simp [deleteOccurrence, different]

/-- Replace exactly the selected occurrence.  Table size and all other tables
are unchanged. -/
def updateOccurrence (state : State schema) (table : schema.Table)
    (occurrence : OccAt state table) (replacement : schema.Row table) :
    State schema :=
  state.setTable table <|
    (state.rows table).set occurrence.index.val replacement occurrence.index.isLt

@[simp] theorem rows_updateOccurrence_same (state : State schema)
    (table : schema.Table) (occurrence : OccAt state table)
    (replacement : schema.Row table) :
    (state.updateOccurrence table occurrence replacement).rows table =
      (state.rows table).set occurrence.index.val replacement occurrence.index.isLt := by
  simp [updateOccurrence]

@[simp] theorem rows_updateOccurrence_other (state : State schema)
    (target table : schema.Table) (occurrence : OccAt state target)
    (replacement : schema.Row target) (different : table ≠ target) :
    (state.updateOccurrence target occurrence replacement).rows table =
      state.rows table := by
  simp [updateOccurrence, different]

/-- Order-insensitive equality of one table, retaining duplicate
multiplicities through `List.Perm`. -/
def TableEquivalent (left right : State schema) (table : schema.Table) : Prop :=
  (left.rows table).toList.Perm (right.rows table).toList

/-- Two states are equivalent when every table contains the same bag of row
occurrences. -/
def Equivalent (left right : State schema) : Prop :=
  ∀ table, TableEquivalent left right table

theorem equivalent_refl (state : State schema) : Equivalent state state := by
  intro table
  exact List.Perm.refl _

theorem equivalent_symm {left right : State schema}
    (equivalent : Equivalent left right) : Equivalent right left := by
  intro table
  exact (equivalent table).symm

theorem equivalent_trans {first second third : State schema}
    (left : Equivalent first second) (right : Equivalent second third) :
    Equivalent first third := by
  intro table
  exact (left table).trans (right table)

end State

end Pgx.Logic
