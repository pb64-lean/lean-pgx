import Lake
open Lake DSL

/-!
Lake provides the editor project model and a developer build. Bazel remains
the authoritative build system.
-/

package «lean-pgx» where
  leanOptions := #[⟨`experimental.module, true⟩]

require «pg-lean» from "../pg-lean"

/- pg-lean's current Lake model omits the Tls library that its connection
   module imports.  Expose the sibling source root here for editor builds;
   Bazel continues to use tls13-lean's authoritative targets. -/
lean_lib «Tls» where
  srcDir := "../tls13-lean"
  roots := #[
    `Tls.Record,
    `Tls.Record.Laws,
    `Tls.Handshake,
    `Tls.Client,
    `Tls.Client.Laws,
    `Tls.Server,
    `Tls.Server.Laws
  ]

@[default_target]
lean_lib «Pgx» where
  srcDir := "lean"
  roots := #[`Pgx]
