module

public section

/-!
# Many-sorted relational schemas

The row type of a table is indexed by the table identity.  A generated row
type is only a carrier of possible values; membership in a particular
database state is introduced separately in `Pgx.Logic.State`.
-/

namespace Pgx.Logic

universe u v

/-- A finite database signature may contain tables with different row
carriers.  Decidable table identity is enough for purely functional updates;
the kernel does not require row equality. -/
structure Schema where
  Table : Type u
  Row : Table → Type v
  tableDecidableEq : DecidableEq Table

attribute [instance] Schema.tableDecidableEq

end Pgx.Logic
