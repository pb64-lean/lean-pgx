# Bazel rule reference

Load the public macros from:

```starlark
load(
    "@lean-pgx//bazel:defs.bzl",
    "lean_pg_library",
    "pg_compat_test",
    "pg_live_test",
    "pg_query_set",
)
```

## `pg_query_set`

Collects literal query sources and their declarative manifest.

```starlark
pg_query_set(
    name = "queries",
    srcs = ["queries/get_user.sql"],
    manifest = "queries/queries.json",
)
```

| Attribute | Required | Description |
| --- | --- | --- |
| `name` | yes | Target name. |
| `srcs` | yes | Nonempty list of `.sql` files. Each basename must be unique and produce a unique Lean module name. |
| `manifest` | yes | One `.json` query manifest. |
| `visibility` | no | Normal Bazel visibility. |
| `**kwargs` | no | Additional attributes accepted by the underlying rule. |

A source basename is converted to PascalCase after removing `.sql`; every
non-alphanumeric character starts a new word. `get_user.sql` becomes
`GetUser`. The result must be nonempty and begin with a letter. The manifest's
`leanName` must equal the derived value.

The rule returns the query sources, manifest, and derived names through
`PgQuerySetInfo`. Most consumers pass the target directly to
`lean_pg_library`.

## `lean_pg_library`

Replays DDL, probes schema and queries, emits generated artifacts, and compiles
the generated Lean modules as a `lean_library`.

```starlark
lean_pg_library(
    name = "app_db",
    module_prefix = "AppDb",
    migrations = [
        "migrations/0001_schema.sql",
        "migrations/0002_tables.sql",
    ],
    queries = ":queries",
    schemas = ["app"],
    canonical_major = 18,
    server_majors = [17, 18],
    deps = ["//lean:extension_codecs"],
    visibility = ["//visibility:public"],
)
```

| Attribute | Required/default | Description |
| --- | --- | --- |
| `name` | required | Compiled Lean library target. Also creates `<name>_gen` and private `<name>_srcs`. |
| `module_prefix` | required | Root generated Lean module, such as `AppDb`. Dots map to directories. |
| `migrations` | required | Ordered `.sql` DDL inputs replayed into an empty database. |
| `queries` | required | A target providing `PgQuerySetInfo`. |
| `schemas` | required | PostgreSQL schema names captured in the contract. |
| `canonical_major` | `18` | Major used for generation; currently `17` or `18`. It must occur in `server_majors`. |
| `postgres` | selected from `canonical_major` | Optional execution-distribution override. Normally omit it so the macro uses its namespaced pinned repository. |
| `server_majors` | `[17, 18]` | Nonempty, duplicate-free majors accepted by generated attachment. Must exactly equal sorted `supportedServerMajors` in the manifest. |
| `deps` | `[]` | Extra Lean dependencies, normally modules exporting custom codecs. |
| `visibility` | package default | Applied to the generated and compiled public-facing targets; private unless the caller's package overrides its default visibility. |
| `**kwargs` | none | Additional `lean_library` attributes. |

The macro adds runtime, local-constraint, and logic dependencies automatically.
Do not repeat them in `deps`.

For target `app_db` and prefix `AppDb`, fixed generation outputs are:

```text
AppDb/Types.lean
AppDb/Schema.lean
AppDb/Constraints.lean
AppDb/Queries/<DerivedQueryName>.lean
AppDb.lean
app_db.pgir.json
app_db.contract.sha256
app_db.compatibility.sha256
```

The `<name>_gen` target provides all outputs by default and these output groups:

| Output group | Contents |
| --- | --- |
| `lean_srcs` | Generated `.lean` modules. |
| `schema_ir` | Canonical `.pgir.json` snapshot. |
| `contract_hash` | Canonical-major contract SHA-256 file. |
| `compatibility_hash` | Major-independent SHA-256 file. |

For example:

```sh
bazel build //db:app_db
bazel build //db:app_db_gen --output_groups=schema_ir
```

The generation target also returns rules_lean's `LeanGeneratedSourceInfo`
provider. Its `lean_srcs` depset matches the output group above, allowing
workspace-wide tooling to discover and build lean-pgx source generators
without depending on lean-pgx-specific provider fields.

Generation starts a private transient PostgreSQL cluster, replays only declared
inputs, and requests a network-blocked Bazel executor. The executor ultimately
determines whether that requirement is enforced.

## `pg_compat_test`

Replays one generated contract against at least two PostgreSQL distributions
and compares their normalized major-independent IR.

```starlark
pg_compat_test(
    name = "app_db_pg17_pg18",
    database = ":app_db",
    majors = [17, 18],
)
```

| Attribute | Required/default | Description |
| --- | --- | --- |
| `name` | required | Test target name. |
| `database` | required | The `lean_pg_library` target whose generated contract is replayed. |
| `postgres` | selected from `majors` | Optional list of execution-distribution overrides. If supplied, its length must equal `majors`. |
| `majors` | `[17, 18]` | At least two unique supported majors. The macro selects its namespaced pinned distribution for each. |
| `visibility` | package default | Normal Bazel visibility; private unless the caller's package overrides its default. |
| `**kwargs` | none | Additional attributes for the comparison test. |

The first snapshot is the comparison baseline. The test ignores the server
major field itself but compares the remaining Lean-level schema/query
semantics. It does not execute application queries for behavioral equivalence.

## `pg_live_test`

Runs a Lean acceptance executable against a fresh cluster migrated from the
same generated contract.

```starlark
pg_live_test(
    name = "app_db_live",
    database = ":app_db",
    runner = ":app_db_acceptance",
    major = 18,
    data = ["testdata/expected.json"],
    args = ["--fixture", "db/testdata/expected.json"],
)
```

| Attribute | Required/default | Description |
| --- | --- | --- |
| `name` | required | Test target name. |
| `database` | required | The `lean_pg_library` whose migrations are replayed. |
| `runner` | required | Executable run by the generated test process inside the server lifecycle. |
| `major` | `18` | Supported server major used by the fixture; it must be accepted by the generated database. |
| `postgres` | selected from `major` | Optional execution-distribution override. Normally omit it; the binary's actual major is verified at test startup. |
| `args` | `[]` | Arguments appended verbatim after generated connection/migration arguments. Relative runfile paths start at the workspace root and therefore include the package path. |
| `data` | `[]` | Additional declared files needed by the runner. |
| `visibility` | package default | Normal Bazel visibility; private unless the caller's package overrides its default. |
| `**kwargs` | none | Additional test-rule attributes. |

The runner receives this command-line shape:

```text
<runner> --url <temporary-url> \
  --migration <first-path> [--migration <next-path> ...] \
  <args...>
```

The test owns server startup, readiness, shutdown, logs on failure, and cleanup.
The runner must replay the supplied migration paths in order before attachment;
the harness deliberately does not interpret application DDL. The macro adds a
`block-network` test tag unless one is already present. The runner should own
and close each client connection it creates. This wrapper currently requires
Bash/POSIX and Bazel directory runfiles; manifest-only runfiles and Windows are
unsupported.

## Providers and compatibility

`PgQuerySetInfo` and `LeanPgGenInfo` are public, pre-release extension points.
The former carries ordered SQL sources, the manifest, and derived Lean module
names. The latter carries generated source/output artifacts, migration and
query inputs, module prefix, canonical/supported majors, and contract hashes.
`LeanGeneratedSourceInfo` is owned by rules_lean and follows that project's
compatibility policy. Prefer the macros and documented output groups unless a
custom rule genuinely needs provider data.

Before the first stable release, provider fields and generated auxiliary target
names may change with an entry in `CHANGELOG.md`. After a stable release they
will follow the repository's published compatibility policy. The public macro
names, attributes, and generated Lean modules are the primary supported API.
