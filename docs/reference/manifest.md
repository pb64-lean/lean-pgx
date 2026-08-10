# Query manifest reference

The query manifest is one JSON object. Query entries are keyed by the exact
basename of each declared `.sql` file. Three reserved root keys configure the
whole generated database:

- `supportedServerMajors`
- `typeOverrides`
- `extensionCodecPackages`

The manifest and `pg_query_set.srcs` must have an exact one-to-one basename
association. Two query paths with the same basename are invalid even if they
are in different directories.

A machine-readable schema is available at
[`query-manifest.schema.json`](query-manifest.schema.json). Some semantic
invariants below require the generator and cannot be expressed fully in JSON
Schema.

## Query entries

```json
{
  "get_user.sql": {
    "leanName": "GetUser",
    "cardinality": "zeroOrOne",
    "parameters": [
      {"position": 1, "name": "id", "nullable": false}
    ]
  }
}
```

Every query entry requires:

| Field | Type | Contract |
| --- | --- | --- |
| `leanName` | string | Must exactly equal the deterministic PascalCase name derived from the SQL basename. |
| `cardinality` | string | One of `execute`, `exactlyOne`, `zeroOrOne`, or `many`. |
| `parameters` | array | One entry for each PostgreSQL positional parameter, or `[]`. |

The derived name removes `.sql`, treats non-alphanumeric characters as word
boundaries, uppercases the first character of each word, and must start with a
letter. For example, `find_user-by_email.sql` derives
`FindUserByEmail`.

Each parameter requires:

| Field | Type | Contract |
| --- | --- | --- |
| `position` | positive integer | Positions must be unique and dense from 1 through *n*. Input order is canonicalized. |
| `name` | string | Nonempty, trimmed, and unique within the query; becomes the Lean `Params` field. |
| `nullable` | Boolean | Whether the generated parameter field is `Option T`. |

PostgreSQL determines each parameter's SQL type from statement description.
The manifest's nullability is an application contract, not an inferred
database property.

Cardinality controls the generated result and is checked at runtime:

| Value | Result |
| --- | --- |
| `execute` | `Pgx.Typed.CommandResult`; returned data rows are rejected. |
| `exactlyOne` | `Row`; zero or multiple rows are rejected. |
| `zeroOrOne` | `Option Row`; multiple rows are rejected. |
| `many` | `Array Row`. |

## `supportedServerMajors`

```json
{
  "supportedServerMajors": [17, 18]
}
```

Optional; defaults to `[17, 18]`. The array must be nonempty, positive, unique,
and sorted into canonical order by the parser. It must exactly equal the
`lean_pg_library.server_majors` list. Current probe adapters support only 17
and 18, so other values fail later even though the JSON shape permits positive
integers.

## Direct `typeOverrides`

Use a direct override for a PostgreSQL type that is not mapped by the runtime:

```json
{
  "typeOverrides": [
    {
      "key": {
        "schema": "ext",
        "name": "vector",
        "kind": "base"
      },
      "leanType": "MyVector.Vector",
      "codec": "MyVector.codec",
      "importModule": "MyVector"
    }
  ]
}
```

`key` is the stable PostgreSQL identity. `kind` is one of `base`, `enum`,
`domain`, `array`, `range`, `multirange`, `composite`, or `pseudo`.
`leanType` names the generated field type. `codec` must name a declaration of
type:

```lean
Pgx.Typed.ResolvedCodec MyVector.Vector
```

`importModule` is optional in the JSON representation. Supply it unless the
type and codec are already visible through generated runtime imports, and add
the module's Bazel target to `lean_pg_library.deps`.

Schema, name, Lean type, codec, and any import module must be nonempty and
trimmed. Type keys must be unique. Unknown and pseudo types without an exact
override fail generation.

## `extensionCodecPackages`

Use a package when multiple overrides belong to one installed PostgreSQL
extension:

```json
{
  "extensionCodecPackages": [
    {
      "extension": "vector",
      "importModule": "PgVector",
      "typeOverrides": [
        {
          "key": {
            "schema": "public",
            "name": "vector",
            "kind": "base"
          },
          "leanType": "PgVector.Vector",
          "codec": "PgVector.codec"
        }
      ]
    }
  ]
}
```

Package rules:

- `extension`, `importModule`, and `typeOverrides` are required;
- the override array is nonempty;
- nested overrides omit `importModule` because the package owns it;
- extension names are unique; and
- a type key cannot occur in both a direct override and a package, or in two
  packages.

Generation requires the named extension to be installed by the declared
migrations. Its observed version and owned type identities become part of the
generated contract and are rechecked during attachment.

## Complete example

```json
{
  "supportedServerMajors": [17, 18],
  "typeOverrides": [],
  "extensionCodecPackages": [],
  "create_user.sql": {
    "leanName": "CreateUser",
    "cardinality": "execute",
    "parameters": [
      {"position": 1, "name": "email", "nullable": false},
      {"position": 2, "name": "displayName", "nullable": true}
    ]
  },
  "list_users.sql": {
    "leanName": "ListUsers",
    "cardinality": "many",
    "parameters": []
  }
}
```

The current parser does not reserve `$schema`; configure schema association in
your editor rather than adding a `$schema` property to the manifest.
