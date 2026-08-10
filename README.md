# lean-pgx

[![CI](https://github.com/pb64-lean/lean-pgx/actions/workflows/ci.yml/badge.svg)](https://github.com/pb64-lean/lean-pgx/actions/workflows/ci.yml)
[![Assurance](https://github.com/pb64-lean/lean-pgx/actions/workflows/assurance.yml/badge.svg)](https://github.com/pb64-lean/lean-pgx/actions/workflows/assurance.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

`lean-pgx` generates checked Lean 4 types and query runners from PostgreSQL
DDL and literal SQL. PostgreSQL performs SQL parsing, name resolution, cast
selection, and statement description; generated code records stable symbolic
identities and verifies a live database before decoding values.

> [!IMPORTANT]
> The project is pre-release. The module version is a development coordinate,
> not a compatibility promise, and public APIs may change before the first
> release.

```text
migrations + .sql files + manifest
                │
                ▼
      transient pinned PostgreSQL
                │
                ▼
 canonical IR + generated Lean modules
                │
                ▼
  attach-time and per-query verification
```

Generation never consults a developer or production database. The Bazel action
starts an empty private cluster, replays only declared migrations, probes the
declared schemas and queries, writes deterministic outputs, and stops it.

## Current scope

The implemented surface includes:

- PostgreSQL 17/18 code generation and compatibility checks, with PostgreSQL
  18 as the default canonical generator;
- generated enums, domains, one-dimensional arrays, composites, ranges, and
  multiranges, plus explicit codecs for extension or application types;
- typed query parameters and rows with `execute`, `exactlyOne`, `zeroOrOne`,
  and `many` cardinality contracts;
- checked attachment, symbolic OID resolution, prepared-statement descriptor
  checks, result verification, and typed drift errors;
- proof-producing local domain and row validation for a conservative subset of
  normalized PostgreSQL `CHECK` expressions; and
- a pure finite relational-state model for selected unique, primary-key,
  foreign-key, and exclusion constraints, with abstract one-row mutation
  specifications.

It does **not** yet provide relational semantics for analyzed queries, a proof
that a live database is represented by a logical state, transaction or
concurrency semantics, or complete PostgreSQL expression/constraint coverage.
See [Support](docs/support.md) for the exact boundary and
[Roadmap](ROADMAP.md) for planned work.

## Prerequisites

- Bazel or Bazelisk using the version in [`.bazelversion`](.bazelversion)
  (currently Bazel 8.5);
- Nix, used by Bazel to build the Lean and PostgreSQL execution tools; and
- a Linux or macOS POSIX host with Bash and Bazel directory runfiles enabled;
  Windows and manifest-only runfiles are not currently supported; and
- while the modules are not published, sibling source checkouts of
  `rules_lean`, `pg-lean`, and `tls13-lean`.

For editor support, install the toolchain named in [`lean-toolchain`](lean-toolchain).
Bazel is the authoritative build; Lake supplies the editor project model.

## Source-checkout consumer setup

Until releases are published, a consuming root module can use local overrides:

```starlark
bazel_dep(name = "lean-pgx", version = "0.1.0")
local_path_override(module_name = "lean-pgx", path = "../lean-pgx")

# Local overrides in a dependency are not inherited by the root module.
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

The `lean-pgx` module extension owns namespaced repositories for its pinned
PostgreSQL, `socat`, and lifecycle tools, so consumers do not declare those
repositories or copy a private Nix extension block. This is an intentionally
temporary source-checkout recipe; [Getting started](docs/getting-started.md) is
the authoritative setup guide while the publication interface is finalized.

## Minimal database target

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

The [complete quickstart](examples/quickstart/README.md) adds a runnable client
and a live transient-PostgreSQL test.

Each query file contains one statement. Its root manifest entry uses the exact
SQL basename and supplies only the application-owned facts PostgreSQL cannot
infer safely:

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

The generated root module exports the database descriptor, attachment
function, types, schema declarations, constraints, logic API, and query
modules. Handle attachment failures before using the checked capability:

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

The owner of `raw` remains responsible for closing it. Treat
`CheckedConnection` as a capability tied to the installed session contract:
do not mutate its session settings, deallocate its cached statements, or
change the checked schema behind it.

## Trust boundary

Lean checks generated validator proofs relative to the generated predicates
and checks the pure relational theorems. PostgreSQL, catalog and protocol
observations, the normalized-expression parser, code generator, emitter, and
runtime I/O remain trusted implementation components. Attachment detects many
forms of drift; it does not turn a live PostgreSQL database into a proved Lean
logical state. Details are in [Assurance and trust](docs/assurance-and-trust.md).

## Documentation

- [Getting started](docs/getting-started.md)
- [Runnable quickstart](examples/quickstart/README.md)
- [Supported and unsupported behavior](docs/support.md)
- [Architecture](docs/architecture.md)
- [Bazel rule reference](docs/reference/bazel-rules.md)
- [Query manifest reference](docs/reference/manifest.md)
- [Generated API reference](docs/reference/generated-api.md)
- [Runtime errors](docs/reference/runtime-errors.md)
- [Design decisions](docs/design/0001-server-authoritative-codegen.md)
- [Roadmap](ROADMAP.md)

## Development

```sh
bazel build //...
bazel test //...
lake update
lake build
```

`bazel test //...` includes unit tests, generation from real DDL in transient
PostgreSQL clusters, cross-major compatibility checks, and a live generated
API acceptance test. See [Contributing](CONTRIBUTING.md) before sending a
change and [Security](SECURITY.md) for private vulnerability reporting.

## License

Licensed under the [Apache License 2.0](LICENSE).
