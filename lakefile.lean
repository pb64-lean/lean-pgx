import Lake
open Lake DSL

/-!
Lake provides the editor project model and a developer build. Bazel remains
the authoritative build system.
-/

package «lean-pgx» where
  version := v!"0.1.0"
  description := "Checked Lean 4 types and query runners generated from PostgreSQL"
  keywords := #["postgresql", "database", "code-generation", "bazel"]
  homepage := "https://github.com/pb64-lean/lean-pgx"
  license := "Apache-2.0"
  leanOptions := #[⟨`experimental.module, true⟩]

require «pg-lean» from "../pg-lean"

@[default_target]
lean_lib «Pgx» where
  srcDir := "lean"
  roots := #[`Pgx]
