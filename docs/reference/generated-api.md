# Generated API reference

This reference describes the stable shape of generated modules. Exact
declaration names depend on the configured module prefix and PostgreSQL
identifiers and may still change during the pre-release period.

Assume this target:

```starlark
lean_pg_library(
    name = "app_db",
    module_prefix = "AppDb",
    migrations = ["migrations/0001.sql"],
    queries = ":queries",
    schemas = ["app"],
)
```

## Module layout

```text
AppDb.Types
AppDb.Schema
AppDb.Constraints
AppDb.Queries.<QueryName>
AppDb
```

`import AppDb` publicly imports all generated modules. Import a narrower module
when an application wants a smaller explicit dependency surface.

Names derived from PostgreSQL identifiers use deterministic Lean-safe casing
and collision allocation. An automatically discovered array type whose natural
name collides with its element type receives a semantic `Array` suffix; for
example, an array of `AppUserStatus` is named `AppUserStatusArray`. Numeric
suffixes remain a last-resort disambiguator for other unavoidable collisions.
Treat generated names as contract outputs and let compilation expose changes
after a DDL update.

## Database descriptor and attachment

The generated schema surface exposes:

```lean
AppDb.database : Pgx.Typed.DatabaseDesc

AppDb.attach (conn : Pg.Connection) :
  Std.Async.Async
    (Except Pgx.Typed.Error (Pgx.Typed.CheckedConnection AppDb.database))
```

`database` contains the symbolic runtime contract. `attach` installs and checks
the session contract, resolves local OIDs, compares supported catalog metadata,
and returns the dependent checked capability.

Attachment does not take ownership of `conn`. The creator must close it. The
public `CheckedConnection.raw` escape hatch exists for operations not generated
by `lean-pgx`, but changing session settings, prepared statements, or schema
objects can invalidate the checked capability.

## Generated types

Generated type namespaces live under `AppDb.Types`.

### Enums

An enum becomes an inductive Lean type plus label conversion, descriptor, and
resolved codec:

```lean
inductive AppUserStatus where
  | pending
  | active
  | disabled

AppDb.Types.AppUserStatus.toLabel
AppDb.Types.AppUserStatus.ofLabel?
AppDb.Types.AppUserStatus.descriptor
AppDb.Types.AppUserStatus.codec
```

Enum labels that cannot be represented directly are allocated safe Lean
constructor names while `toLabel` preserves the PostgreSQL spelling.

### Domains and refined values

A locally modeled domain exposes an unrefined constructor shape and a
proof-bearing value:

```lean
namespace AppDb.Types.AppEmailAddress

structure Data where
  toBase : String

def ValidPred : Data → Prop
abbrev Value := { value : Data // ValidPred value }
def validate : Data → Except Pgx.ConstraintViolation Value
theorem validate_sound ...
theorem validate_complete ...
def toBase : Value → String
def descriptor : Pgx.Typed.StaticTypeDesc
def codec : Pgx.Typed.ResolvedCodec Value

end AppDb.Types.AppEmailAddress
```

The outer generated name is also abbreviated to its `Value`, so query fields
normally use `AppDb.Types.AppEmailAddress`. Construct it with `validate`, not by
assuming the database check.

### Containers and composites

Generated aliases use:

```lean
Pgx.Typed.PgArray α       -- Array (Option α), one dimension
Pgx.Typed.PgRange α       -- empty or a span with optional finite bounds
Pgx.Typed.PgMultirange α  -- Array (PgRange α)
```

Each generated container namespace supplies its static descriptor and resolved
codec. Element values may themselves be generated/refined types.

A named PostgreSQL composite becomes a generated `Data` structure and codec.
Every field is an `Option`, even when the same composite is a table row type:
PostgreSQL table `NOT NULL` constraints do not constrain a standalone composite
value. Local field/domain/type-modifier checks may wrap the composite in a
proof-bearing `Value` using the same validation pattern.

## Schema rows

Each relation appears under its schema and relation namespace, for example:

```lean
AppDb.Schema.App.Users.Data
AppDb.Schema.App.Users.ValidPred
AppDb.Schema.App.Users.Row
AppDb.Schema.App.Users.validate
AppDb.Schema.App.Users.validate_sound
AppDb.Schema.App.Users.validate_complete
AppDb.Schema.App.Users.descriptor
```

`Data` contains generated Lean fields. `Row` is a subtype proving all emitted
local row checks and type modifiers represented by `ValidPred`. This is a
single-row/local proposition: unique, foreign-key, and exclusion constraints
do not refine an individual `Row`.

## Query modules

For a manifest entry whose `leanName` is `GetUser`, generation creates
`AppDb.Queries.GetUser` with:

```lean
structure Params where
  id : Int64

structure RowData where
  id : Int64
  email : String

def ValidPred : RowData → Prop
abbrev Row := { value : RowData // ValidPred value }
def validate : RowData → Except Pgx.ConstraintViolation Row
def spec : Pgx.Typed.QuerySpec AppDb.database Params Row .zeroOrOne

def run
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (params : Params) :
    Std.Async.Async (Except Pgx.Typed.Error (Option Row))
```

Application code should rely on the generated `Row` name and use `row.val` to
access its `RowData`. Nullable parameters and columns become `Option`. Query
result nullability is conservative, especially around expressions and outer
joins.

`run` returns according to the manifest cardinality:

| Cardinality | Return payload |
| --- | --- |
| `execute` | `Pgx.Typed.CommandResult` |
| `exactlyOne` | `Row` |
| `zeroOrOne` | `Option Row` |
| `many` | `Array Row` |

`CommandResult.tag` is PostgreSQL's command tag. It is not a generated proof of
an affected-row count.

## Constraint metadata

`AppDb.Constraints` exposes normalized catalog data, including:

```lean
AppDb.Constraints.all
AppDb.Constraints.indexes
AppDb.Constraints.views
AppDb.Constraints.routines
AppDb.Constraints.extensionCodecPackages
```

These arrays are descriptors used for inspection and runtime checking. Their
presence does not imply that every item has an executable Lean proposition.

## Relational logic

`AppDb.Logic` is generated for relation-shaped schema objects:

- `Table`, a tag for each generated relation;
- `Row : Table → Type`, mapping tags to generated row data;
- `schema` and `State`, the many-sorted finite state;
- per-relation `At state` and duplicate-sensitive `OccAt state` aliases;
- key projection structures and catalog lifecycle metadata;
- `Semantics`, whose fields interpret exact equality/exclusion operators;
- per-constraint `Holds` for the modeled relational subset;
- `modeledConstraints` and `unsupportedRelationalConstraints` inventories;
- `IntegrityContext semantics phase state`; and
- per-table `insertSpec`, `deleteSpec`, and `updateSpec`.

The state stores row occurrences in arrays and therefore models bags rather
than sets. `Semantics` is an explicit caller input; neither live execution nor
attachment manufactures PostgreSQL operator laws. Mutation declarations are
pure one-occurrence transition relations, not functions that issue DML.

See [Support](../support.md) for the exact modeled subset and deferred query,
snapshot, certification, transaction, and concurrency semantics.

## Custom codecs

A manifest override names a declaration of this shape:

```lean
def codec : Pgx.Typed.ResolvedCodec MyType := {
  expected := ...
  encode := ...
  decode := ...
}
```

The codec receives a symbolic type resolver and the type resolved for this
connection. It must validate any OIDs it consumes and return `Pgx.Typed.Error`
on mismatch. Generated arrays, composites, ranges, and domains can call nested
resolved codecs, so a text-only or binary-only implementation must reject wire
formats it cannot interpret rather than reinterpret bytes silently.
