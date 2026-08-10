import Lake
open Lake DSL

/-!
Lake provides the editor project model and a developer build. Bazel remains
the authoritative build system.
-/

package «lean-pgx» where
  leanOptions := #[⟨`experimental.module, true⟩]

require «pg-lean» from "../pg-lean"

@[default_target]
lean_lib «Pgx» where
  srcDir := "lean"
  roots := #[`Pgx]
