# Getting started

This guide creates a generated Lean database library from ordered DDL and one
literal query. `lean-pgx` is currently consumed from source checkouts; no
stable release or Bazel Central Registry entry is promised yet.

## 1. Prepare the workspace

Use sibling repositories so all temporary local overrides resolve:

```text
workspace/
├── my-service/
├── lean-pgx/
├── pg-lean/
├── rules_lean/
└── tls13-lean/
```

Install Nix and Bazel or Bazelisk. `lean-pgx` currently selects Bazel 8.5 in
its own checkout. For Lean-aware editors, also install the toolchain selected
by `lean-pgx/lean-toolchain`:

```sh
elan toolchain install leanprover/lean4-nightly:nightly-2026-04-25
```

If a language server was already running, restart it after selecting the
toolchain.

## 2. Add the Bazel modules

In the consuming root `MODULE.bazel`:

```starlark
bazel_dep(name = "lean-pgx", version = "0.1.0")
local_path_override(module_name = "lean-pgx", path = "../lean-pgx")

bazel_dep(name = "rules_lean", version = "0.1.0")
local_path_override(module_name = "rules_lean", path = "../rules_lean")

bazel_dep(name = "pg-lean", version = "0.1.0", repo_name = "pg_lean")
local_path_override(module_name = "pg-lean", path = "../pg-lean")

bazel_dep(name = "tls13-lean", version = "0.1.0", repo_name = "tls13_lean")
local_path_override(module_name = "tls13-lean", path = "../tls13-lean")

lean = use_extension("@rules_lean//lean:extensions.bzl", "lean")
lean.nix_toolchain(
    name = "lean4",
    attr = "lean4_upstream_std",
    nix_file = "@rules_lean//:nixpkgs.nix",
    nix_file_deps = ["@rules_lean//:nixpkgs.json"],
)
use_repo(lean, "lean4_toolchain")
register_toolchains("@lean4_toolchain//:all")
```

Bzlmod ignores local overrides declared by dependency modules, which is why
the root repeats the sibling overrides. The `lean-pgx` module extension owns
namespaced repositories for its PostgreSQL, `socat`, and coreutils execution
dependencies. Consumers neither import that extension directly nor copy its
repository declarations.

The block above registers the same pinned Nix-backed Lean toolchain used by the
tested downstream fixture. A consumer that already owns a compatible Lean
toolchain may register that instead.

## 3. Declare DDL

Put migrations in the exact order in which a new database should receive
them. For example, `db/migrations/0001_users.sql`:

```sql
CREATE SCHEMA app;

CREATE TABLE app.users (
  id bigint GENERATED ALWAYS AS IDENTITY PRIMARY KEY,
  email text NOT NULL UNIQUE,
  display_name text NOT NULL
);
```

The generation action starts from an empty cluster and replays only the files
listed on the target. Migrations should therefore be deterministic and
self-contained. The action never reads the schema from a running application
database.

## 4. Add a literal query and manifest

Create `db/queries/get_user.sql`:

```sql
SELECT id, email, display_name
FROM app.users
WHERE id = $1;
```

Each declared `.sql` file contains one statement. Create
`db/queries/queries.json`:

```json
{
  "supportedServerMajors": [17, 18],
  "get_user.sql": {
    "leanName": "GetUser",
    "cardinality": "zeroOrOne",
    "parameters": [
      {"position": 1, "name": "id", "nullable": false}
    ]
  }
}
```

Configure the machine-readable schema in your editor rather than adding a
`$schema` root property: the current generator treats every unreserved root
key as a query. See the [manifest reference](reference/manifest.md) for the
schema path and exact invariants.

> [!NOTE]
> `cardinality` and parameter nullability are application contracts. PostgreSQL
> supplies SQL parameter/result types, but does not prove those two facts.

## 5. Define the database library

In `db/BUILD.bazel`:

```starlark
load("@lean-pgx//bazel:defs.bzl", "lean_pg_library", "pg_query_set")

pg_query_set(
    name = "queries",
    srcs = ["queries/get_user.sql"],
    manifest = "queries/queries.json",
)

lean_pg_library(
    name = "app_db",
    module_prefix = "AppDb",
    migrations = ["migrations/0001_users.sql"],
    queries = ":queries",
    schemas = ["app"],
    visibility = ["//visibility:public"],
)
```

Build it with:

```sh
bazel build //db:app_db
```

The target runs pinned PostgreSQL 18 by default to generate the contract and
then compiles the generated Lean library. Set `canonical_major = 17` to select
the supported PostgreSQL 17 generator; the canonical major must also occur in
`server_majors`. Generated sources and artifacts are Bazel outputs; do not
check in or edit copied versions.

## 6. Attach and run

Import the generated root module. Attachment returns a typed `Except`; handle
that error before a query receives the checked connection:

```lean
import AppDb

open Std.Async

private def typed! (context : String) (result : Except Pgx.Typed.Error α) :
    Async α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")

def findUser (raw : Pg.Connection) (id : Int64) :
    Async (Option AppDb.Queries.GetUser.Row) := do
  let checked ← typed! "attach AppDb" (← AppDb.attach raw)
  typed! "GetUser" (← AppDb.Queries.GetUser.run checked { id })
```

The code that created `raw` must close it. A checked connection owns prepared
statement cache state but not the underlying connection lifetime. Do not use
the raw escape hatch to change session settings, deallocate generated prepared
statements, or alter checked objects while the capability is active.

## 7. Add compatibility and live tests

Add a cross-major contract test when both pinned distributions are in scope:

```starlark
load("@lean-pgx//bazel:defs.bzl", "pg_compat_test")

pg_compat_test(
    name = "app_db_pg17_pg18",
    database = ":app_db",
    majors = [17, 18],
)
```

The macro selects its namespaced pinned distribution for each major. Use
`pg_live_test(major = 18, ...)` for an executable that must exercise the
generated API against a fresh server. The rule supplies `--url URL`, followed
by one `--migration PATH` per declared migration, before custom arguments. The
runner must replay those files in order before attachment. See the
[Bazel rule reference](reference/bazel-rules.md).

## Next steps

- Review the [support matrix](support.md) before relying on a PostgreSQL type,
  constraint form, or logical proposition.
- Read the [generated API reference](reference/generated-api.md).
- Plan operational handling for [runtime errors](reference/runtime-errors.md).
- Understand the [assurance and trust boundary](assurance-and-trust.md).
