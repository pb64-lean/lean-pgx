"""Exact principal-theorem statements for lean-pgx's public runtime audit."""

PGX_PRINCIPAL_TYPES = {
    "Pgx.Constraint.validate_sound": "∀ {α : Type _} (checks : List (Pgx.Constraint.Check α)) {value : α} {refined : { candidate : α // Pgx.Constraint.Valid checks candidate }}, Pgx.Constraint.validate checks value = Except.ok refined → refined.val = value ∧ Pgx.Constraint.Valid checks value",
    "Pgx.Constraint.validate_complete": "∀ {α : Type _} (checks : List (Pgx.Constraint.Check α)) {value : α}, Pgx.Constraint.Valid checks value → ∃ refined, Pgx.Constraint.validate checks value = Except.ok refined",
    "Pgx.Logic.State.equivalent_refl": "∀ {schema : Pgx.Logic.Schema.{_, _}} (state : Pgx.Logic.State schema), Pgx.Logic.State.Equivalent state state",
    "Pgx.Logic.State.equivalent_symm": "∀ {schema : Pgx.Logic.Schema.{_, _}} {left right : Pgx.Logic.State schema}, Pgx.Logic.State.Equivalent left right → Pgx.Logic.State.Equivalent right left",
    "Pgx.Logic.State.equivalent_trans": "∀ {schema : Pgx.Logic.Schema.{_, _}} {first second third : Pgx.Logic.State schema}, Pgx.Logic.State.Equivalent first second → Pgx.Logic.State.Equivalent second third → Pgx.Logic.State.Equivalent first third",
}
