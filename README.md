# lean-pgx

`lean-pgx` generates checked Lean 4 records and query runners from PostgreSQL
DDL and literal SQL. PostgreSQL itself performs SQL parsing, name resolution,
cast selection, and result description; generated code stores only symbolic
schema/type identities and verifies the live descriptors before decoding.

Milestone 1 includes:

- deterministic schema/query IR for schemas, enums, domains, tables, columns,
  constraints, indexes, parameters, result columns, and cardinality;
- a pinned PostgreSQL 18.2 generation action and PostgreSQL 17.8 compatibility
  test;
- generated enum codecs, branded domains, `Params`, `Row`, and checked runners;
- conservative result nullability (`Option` whenever non-null cannot be
  established);
- runtime symbolic OID resolution, schema attachment, prepared-descriptor
  verification, and typed `SchemaDrift`/`QueryDrift` errors;
- explicit type overrides and hard generation errors for unsupported types.

## Bazel usage

The build expects `rules_lean`, `pg-lean`, and `tls13-lean` as sibling
checkouts. The local module pins PostgreSQL through Nix; the ordinary build
does not use a developer or production database.

```starlark
load(
    "@lean-pgx//bazel:defs.bzl",
    "lean_pg_library",
    "pg_compat_test",
    "pg_query_set",
)

pg_query_set(
    name = "queries",
    srcs = [
        "queries/get_user.sql",
        "queries/list_users.sql",
    ],
    manifest = "queries/queries.json",
)

lean_pg_library(
    name = "app_db",
    module_prefix = "AppDb",
    migrations = [
        "migrations/0001_schema.sql",
        "migrations/0002_tables.sql",
    ],
    queries = ":queries",
    schemas = ["app"],
)

pg_compat_test(
    name = "app_db_pg17_pg18",
    database = ":app_db",
    postgres = [
        "@postgresql_17//:toolchain",
        "@postgresql_18//:toolchain",
    ],
)
```

Each query file must contain one statement. Its manifest entry supplies the
Lean module name, parameter names/nullability, and runtime-checked cardinality;
PostgreSQL infers all SQL types.

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

The declared generation outputs are fixed:

```text
AppDb/Types.lean
AppDb/Schema.lean
AppDb/Constraints.lean
AppDb/Queries/GetUser.lean
AppDb/Queries/ListUsers.lean
AppDb.lean
app_db.pgir.json
app_db.contract.sha256
app_db.compatibility.sha256
```

The action initializes a private cluster, binds only a loopback port, replays
the declared migrations in order, probes the declared schemas and queries,
writes those outputs, and stops the server. The PostgreSQL client dependency
currently exposes TCP connections, so the private action uses loopback rather
than a Unix-domain socket.

## Generated runtime API

```lean
import AppDb

def findUser
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (id : Int64) :
    Std.Async.Async
      (Except Pgx.Typed.Error (Option AppDb.Queries.GetUser.Row)) :=
  AppDb.Queries.GetUser.run conn { id }
```

Obtain the checked capability from a raw `Pg.Connection`:

```lean
let checked ← AppDb.attach raw
```

Attachment installs and verifies the generated session contract, checks the
server major, resolves every symbolic type/relation against local OIDs, and
compares schema descriptors. Each query's first use prepares with resolved
parameter OIDs and compares the returned parameter/result descriptors before
binding or decoding.

The generated runners map cardinality to results as follows:

| Manifest value | Lean result |
| --- | --- |
| `execute` | `Pgx.Typed.CommandResult` |
| `exactlyOne` | `Row` |
| `zeroOrOne` | `Option Row` |
| `many` | `Array Row` |

## Type overrides

Arrays, ranges, composites, pseudo-types, and unrecognized extension types are
rejected in Milestone 1 unless the manifest declares an override:

```json
{
  "typeOverrides": [
    {
      "key": {"schema": "ext", "name": "vector", "kind": "base"},
      "leanType": "MyVector.Vector",
      "codec": "MyVector.codec",
      "importModule": "MyVector"
    }
  ]
}
```

The `codec` declaration must have type
`Pgx.Typed.ResolvedCodec MyVector.Vector`; add its Bazel Lean target to the
`deps` of `lean_pg_library`.

## Build and tests

```sh
bazel build //...
bazel test //...
```

The end-to-end fixture in `examples/app_db` exercises DDL replay, all four
cardinalities, enum/domain generation, conservative outer-join nullability,
shifted user OIDs, runtime cardinality checks, `QueryDrift`, `SchemaDrift`, and
PostgreSQL 17/18 compatibility.

Lake supplies the editor project model; Bazel remains authoritative:

```sh
lake update
lake build
```
