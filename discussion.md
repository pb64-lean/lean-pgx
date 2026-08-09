# Discussion

Background discussion for the lean-pgx design. A grain of salt: the discussion did not have context on the existence of lean-pgx as a separate repo or its project structure.

## Prompt

> Consider the repo https://github.com/pb64-lean/pg-lean as a dep and a starting point for a Lean 4 Postgres client.
Structurally, and for context, we might use patterns found in https://github.com/pb64-lean/grpc-lean and https://github.com/pb64-lean/protovalidate-lean where Bazel rules generate Lean source from proto and build a library, with protobuf and gRPC runtimes enabling practical use of the built libraries.
> Our target is to implement language level type support for Postgres interactions, especially prioritizing the definition of checked types for records returned by queries. One approach, with jOOQ as the corresponding reference point, would use codegen against either a DDL or a live DB connection to procure a model of the schema that could then be used for literal Lean 4 code generation - the build process would parallel grpc-lean's codegen from proto approach with custom Bazel rules. Another potential approach is also motivated by grpc-lean, in particular the protobuf notation seen in /home/bill/workspaces/pb64-lean/grpc-lean/third_party/Lean-zh/protobuf/Protobuf/Notation/Message.lean /home/bill/workspaces/pb64-lean/grpc-lean/third_party/Lean-zh/protobuf/Protobuf/Internal/Desc.lean and others, where proto syntax or a sufficient subset is modeled within Lean, removing the need for a distinct parser while encoding source grammar semantics that are useful in proofs. For PostgreSQL 17/18, the analog would be notation support for a constrained subset of the language that is sufficient for typical straightforward DDL scripts in real-world applications. E.g. creating schemas, tables, indices, constraints, and types would likely cover a broad swath of DDL needs - this or a natural extension of it would be a reasonable first support milestone.
For checking queries that will be made at runtime, we can impose reasonable constraints on what is admissible, for instance compile-time literal queries modulo declared parameters, matching sqlx as another well-known reference point for patterns. The approach should do whatever works and is idiomatic, but one option is to represent a parameterized query as a table-valued function in the schema.
An important eventual feature to design for is the translation of PostgreSQL constraints and guarantees into Lean propositions that refine the basic data type into a subtype bearing the proposition, analogous to the protovalidate-lean pattern of Message subtypes with propositions translated from CEL expressions.

> Make a justified choice between these two disjoint approaches, then lock in the selection and and map out the design of only that one selected option.

## Response

Adopt **external, server-authoritative code generation**, with the normal build driven by DDL replayed into a hermetic PostgreSQL instance.

The selected architecture is:

> **DDL migrations + literal query files → pinned PostgreSQL 17/18 semantic analysis → canonical schema/query IR → generated Lean 4 modules → `lean_library`.**

PostgreSQL DDL notation will **not** be added to Lean, and Lean elaboration will not contact a database or parse PostgreSQL syntax.

This choice follows from the primary objective: statically typed query parameters and result records. PostgreSQL already exposes the parameter and result types of an analyzed statement through `Parse` and `Describe`; `pg-lean` already implements that exchange and represents the result as a `Statement` containing parameter OIDs and result-column descriptions. PostgreSQL's `RowDescription` also supplies names, type OIDs, type modifiers, and column provenance where available. ([GitHub][1])

A Lean DDL notation would formalize only one input language. It would not eliminate the substantially harder requirement to reproduce PostgreSQL's query analyzer: name resolution, casts, overloaded functions and operators, domains, extensions, `search_path`, polymorphic types, generated columns, and version-dependent catalog behavior. The external approach instead makes PostgreSQL itself the semantic authority while still generating a formal schema model into Lean. This is also the direct analogue of jOOQ's schema reverse engineering and SQLx's build-time checking of literal queries. ([jOOQ][2])

The accepted cost is that code generation needs a PostgreSQL binary and is heavier than a pure elaborator. Bazel caching, one database instance per generation action, and a separate compatibility test keep that cost controlled.

---

## 1. Authoritative inputs

A generated library has three source inputs:

1. **An ordered migration sequence** capable of creating the database from an empty cluster.
2. **Literal `.sql` query files**, one statement per file.
3. **A small declarative query manifest** containing facts PostgreSQL does not report, principally parameter names, parameter nullability, and expected result cardinality.

The ordinary build does not connect to a developer or production database. It starts a pinned PostgreSQL distribution inside the Bazel action sandbox, applies the migrations, probes the resulting catalog, and stops the server before the action exits.

A live-database importer may later emit a checked-in schema/query snapshot, analogous to SQLx offline metadata, but network access should never be part of the cacheable `lean_pg_library` build action.

### Query example

`queries/get_user.sql`:

```sql
SELECT
  u.id,
  u.email,
  u.status
FROM app.users AS u
WHERE u.id = $1
```

`queries/queries.json`:

```json
{
  "get_user.sql": {
    "leanName": "GetUser",
    "cardinality": "zeroOrOne",
    "parameters": [
      {
        "position": 1,
        "name": "id",
        "nullable": false
      }
    ]
  }
}
```

The SQL type of `$1` is not repeated in the manifest. PostgreSQL infers it during `Parse`. If the expression is genuinely ambiguous, the query author resolves it explicitly:

```sql
WHERE u.id = $1::app.user_id
```

The extended protocol itself rejects more than one statement in a parsed query, which gives an appropriate boundary for generated query contracts. ([PostgreSQL][3])

---

## 2. Bazel surface

A proposed public API is:

```starlark
load(
    "@pg_lean//bazel:defs.bzl",
    "pg_query_set",
    "lean_pg_library",
    "pg_compat_test",
)

pg_query_set(
    name = "app_queries",
    srcs = [
        "queries/get_user.sql",
        "queries/list_projects.sql",
        "queries/create_order.sql",
    ],
    manifest = "queries/queries.json",
)

lean_pg_library(
    name = "app_db",
    module_prefix = "AppDb",
    migrations = [
        "migrations/0001_base.sql",
        "migrations/0002_projects.sql",
        "migrations/0003_orders.sql",
    ],
    queries = ":app_queries",
    schemas = ["app"],
    postgres = "@postgresql_18//:toolchain",
    deps = [
        "@pg_lean//:pg_typed",
    ],
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

Internally, `lean_pg_library` should follow the existing `grpc-lean` division:

* `<name>_gen` is a custom rule that declares and emits Lean sources.
* A provider carries those sources and generation metadata.
* The public macro wraps them in `lean_library`.

That is already the pattern used by `lean_proto_library`, whose provider carries generated Lean sources and whose macro compiles them into a Lean library. ([GitHub][4])

A corresponding provider might be:

```starlark
LeanPgGenInfo = provider(
    fields = {
        "lean_srcs": "Generated Lean source files",
        "schema_ir": "Canonical schema and query snapshot",
        "module_prefix": "Root Lean module",
        "contract_hash": "Semantic contract fingerprint",
        "query_names": "Generated query identifiers",
    },
)
```

### Declared outputs

Bazel must know output paths during analysis, before the database has been inspected. Therefore generation should not create an unknown module per discovered table.

Use a fixed schema split plus one known module per input query:

```text
AppDb/Types.lean
AppDb/Schema.lean
AppDb/Constraints.lean
AppDb/Queries/GetUser.lean
AppDb/Queries/ListProjects.lean
AppDb/Queries/CreateOrder.lean
AppDb.lean
app_db.pgir.json
```

The per-query paths are known from the manifest. Tables and other catalog objects are placed in namespaces inside `Schema.lean`, rather than determining file names dynamically.

---

## 3. Generation action

The generator should itself be a Lean executable, built against `pg-lean`. This reuses the actual client that generated applications will use and avoids a second implementation of the PostgreSQL protocol.

A single Bazel action performs the following sequence.

### 3.1 Create the database

The PostgreSQL toolchain supplies at least:

```text
initdb
postgres
pg_ctl, or equivalent lifecycle support
extension libraries declared by the target
```

The action:

* creates a temporary cluster;
* uses a Unix-domain socket with TCP disabled;
* fixes encoding, locale, timezone, and relevant session settings;
* starts PostgreSQL;
* applies all migration files in declared order;
* treats any SQL error as generation failure.

Migration inputs must be SQL, not `psql` metacommands. Extensions must be declared Bazel inputs rather than discovered from the host.

PostgreSQL 18 is the canonical generation target. PostgreSQL 17 support is checked by a separate target that replays the same inputs and compares normalized contracts. This separation avoids doubling the cost of every normal build while still preventing accidental use of PostgreSQL-18-only semantics. `pg-lean` already exercises its protocol support against both PostgreSQL 17 and 18. ([GitHub][5])

### 3.2 Probe the catalog

The generator reads the relevant system catalogs and normalizes them into a version-independent IR. At minimum:

* namespaces;
* base, enum, domain, array, range, multirange, and composite types;
* relations and columns;
* primary, unique, foreign-key, exclusion, check, and not-null constraints;
* indexes;
* routines;
* collations and type modifiers relevant to generated types.

PostgreSQL's catalogs expose the necessary raw information: `pg_type` models base, enum, domain, and composite types; `pg_attribute` records column types, type modifiers, nullability, identity and generated-column information; and `pg_constraint` records the main constraint classes. ([PostgreSQL][6])

The probe layer must be explicitly versioned. For example, PostgreSQL 17 represents relation-level not-null information principally through `pg_attribute`, whereas PostgreSQL 18 also exposes richer not-null constraint information in `pg_constraint`. These differences should disappear in the normalized IR rather than leaking into code generation. ([PostgreSQL][7])

### 3.3 Analyze every query

For each literal query:

1. Set the target's declared `search_path` and session contract.
2. Send `Parse` with no supplied parameter types.
3. Send `Describe` for the prepared statement.
4. Record `ParameterDescription`.
5. Record `RowDescription`.
6. Determine conservative result nullability.
7. Reject unsupported or unresolved SQL types.
8. Emit a normalized `QueryIR`.

This maps directly onto `pg-lean`'s current `prepare` operation, which folds `ParameterDescription` and `RowDescription` into a `Statement`; its existing `execute` operation then handles bind formats, parameters, portal description, execution, and synchronization. ([GitHub][1])

---

## 4. Canonical intermediate representation

The IR is the central architectural boundary. PostgreSQL-specific probing occurs before it; Lean source generation and proofs operate after it.

```lean
structure TypeKey where
  schema : String
  name   : String
  kind   : TypeKind

structure TypeRef where
  key    : TypeKey
  typmod : Option Int32

structure ColumnIR where
  name       : String
  ty         : TypeRef
  nullable   : Bool
  origin     : Option ColumnKey
  collation  : Option CollationKey

structure ParamIR where
  position   : Nat
  name       : String
  ty         : TypeRef
  nullable   : Bool

structure QueryIR where
  name        : String
  sql         : String
  sqlHash     : UInt64
  params      : Array ParamIR
  columns     : Array ColumnIR
  cardinality : Cardinality
```

The complete `DatabaseIR` additionally contains:

```text
server major and feature set
session/search-path contract
schemas
types
relations and columns
constraint expressions
indexes and keys
routines
queries
required extensions and versions
```

### Symbolic type identity

Generated code must not embed user-defined OIDs.

OIDs are internal catalog identifiers; automatically assigned OIDs are not stable between installations. The generated contract therefore stores symbolic identities such as:

```text
(pg_catalog, int4, base)
(app, user_status, enum)
(app, email_address, domain)
```

OIDs are used only as temporary join keys while probing a particular database. At runtime, symbolic keys are resolved to the actual OIDs of the connected database. ([PostgreSQL][8])

This rule applies equally to table OIDs found in `RowDescription`.

### Fingerprint

The generator computes a deterministic `contractHash` over type-relevant semantics:

* names and kinds of generated types;
* enum labels;
* domain bases;
* relation column order, names, types, type modifiers, and nullability;
* supported local constraints;
* query parameter and result contracts;
* session settings and PostgreSQL major version.

Owners, ACLs, physical OIDs, statistics, and performance-only index properties are excluded. Indexes and relational constraints remain in the IR, but only their semantically relevant parts enter the contract hash.

---

## 5. Query result typing

### 5.1 Admissible queries

The initial generated-query language is deliberately constrained:

* SQL must come from a declared `.sql` file.
* Exactly one statement is allowed.
* Parameters must be positional and dense: `$1` through `$n`.
* Every parameter type must resolve to a concrete supported PostgreSQL type.
* Every result column must have a nonempty, unique name.
* Result types may not remain `record`, `unknown`, or unresolved polymorphic pseudo-types.
* `SELECT` and DML with `RETURNING` are supported.
* A statement with no returned columns is generated as an execution command.
* Dynamic SQL fragments, dynamic identifiers, and runtime-built SQL are outside the typed API.

Unrestricted SQL remains available through the underlying `pg-lean` connection, but its result is the existing raw `Rows` representation rather than a generated record.

### 5.2 Parameter types

PostgreSQL supplies parameter type OIDs but not parameter names or a nullability contract. Therefore:

* type is inferred by PostgreSQL;
* name comes from the query manifest;
* nullability comes from the query manifest;
* a nonnullable parameter is represented by `α`;
* a nullable parameter is represented by `Option α`.

The manifest's nullability is a caller contract, not a claim inferred from the SQL expression.

### 5.3 Result column types

Result names and SQL types come directly from `RowDescription`. PostgreSQL supplies, for each field:

* name;
* source table OID and attribute number when identifiable;
* type OID;
* type size;
* type modifier;
* wire format. ([PostgreSQL][9])

The build-time OID is immediately converted to a symbolic `TypeKey`.

### 5.4 Conservative nullability

PostgreSQL does not include result nullability in `RowDescription`. The generator therefore uses a one-sided analysis:

1. **Start nullable.**
2. A result may become nonnullable only when it has identifiable base-column provenance and the catalog marks that column or domain nonnullable.
3. Run `EXPLAIN (VERBOSE, FORMAT JSON)` using a forced generic plan and restore nullability for outputs occurring on the nullable side of an outer or full join.
4. Expressions, unresolved provenance, unsupported plan shapes, and any analysis uncertainty remain nullable.

This follows the practical SQLx technique of combining `pg_attribute.attnotnull` with an `EXPLAIN VERBOSE` outer-join correction, but strengthens it by making unknown cases nullable rather than optimistic. ([GitHub][10])

The resulting mapping is:

```text
proven non-null       → α
possibly null/unknown → Option α
```

An incorrect non-null inference still cannot manufacture an invalid Lean value. `pg-lean`'s decoder treats a database `NULL` as an error for an ordinary type and accepts it only through the `Option` decoder.

Thus the failure mode is a typed `UnexpectedNull` contract error, not unsound construction.

### 5.5 Cardinality

PostgreSQL does not generally prove whether a query returns zero, one, or many rows. Cardinality is therefore an explicit runtime-checked contract:

```lean
inductive Cardinality
  | execute
  | exactlyOne
  | zeroOrOne
  | many
```

The generated return types are:

```text
execute    → CommandResult
exactlyOne → Row
zeroOrOne  → Option Row
many       → Array Row
```

`exactlyOne` fails on zero or multiple rows; `zeroOrOne` fails on multiple rows. The type communicates the intended application contract without pretending that arbitrary SQL cardinality has been statically proven.

### 5.6 Table-valued functions

Table-valued functions are supported as ordinary schema routines and query sources, but they are not the canonical query representation.

They are useful when an application deliberately wants a stable database-side API: PostgreSQL records argument types, argument modes, and output names, and output argument names determine result-column names. ([PostgreSQL][11])

Nevertheless, `RETURNS TABLE` does not by itself express exact cardinality or complete nullability. The generated client therefore still analyzes the literal call with `Parse` and `Describe`. Application queries remain `.sql` files; a table-valued function is an optional schema abstraction, not a second checking mechanism.

---

## 6. Generated Lean API

For the example query, code generation should produce an interface resembling:

```lean
namespace AppDb.Queries.GetUser

structure Params where
  id : AppDb.Types.UserId

structure RowData where
  id     : AppDb.Types.UserId
  email  : AppDb.Types.EmailAddress
  status : AppDb.Types.UserStatus

structure ValidPred (x : RowData) : Prop where
  emailValid : AppDb.Types.EmailAddress.ValidPred x.email.toBase

abbrev Row := { x : RowData // ValidPred x }

def spec :
    Pg.Typed.QuerySpec
      AppDb.database
      Params
      Row
      .zeroOrOne :=
  {
    sql := "SELECT u.id, u.email, u.status ..."
    params := generatedParamSpecs
    columns := generatedColumnSpecs
    encode := encodeParams
    decode := decodeRow
  }

def run
    (conn : Pg.Typed.CheckedConnection AppDb.database)
    (params : Params) :
    Std.Async.Async
      (Except Pg.Typed.Error (Option Row)) :=
  Pg.Typed.fetchOptional spec conn params

end AppDb.Queries.GetUser
```

The public API has no numeric column indices and no user-written decoding casts. Query-specific code owns:

* SQL text;
* parameter encoding order;
* expected parameter types;
* expected result names and types;
* per-column wire formats;
* raw row decoding;
* constraint validation;
* cardinality checking.

Generated table types follow the same raw/refined division:

```lean
namespace AppDb.Schema.App.Users

structure Data where
  id     : AppDb.Types.UserId
  email  : AppDb.Types.EmailAddress
  status : AppDb.Types.UserStatus
  age    : Option Int32

structure ValidPred (x : Data) : Prop where
  ageNonnegative :
    match x.age with
    | none   => True
    | some n => 0 ≤ n

abbrev Row := { x : Data // ValidPred x }

def validate :
    Data → Except Pg.ConstraintViolation Row := ...

theorem validate_sound ...
theorem validate_complete ...

end AppDb.Schema.App.Users
```

---

## 7. Typed runtime added to `pg-lean`

The existing `PgDecode` and `PgEncode` classes remain the low-level codec layer. They already map wire OIDs and formats to Lean values and include strict versus optional null handling. ([GitHub][12])

A new stable runtime layer should be added above them.

### Core declarations

```lean
namespace Pg.Typed

structure DatabaseDesc where
  serverMajors : Array Nat
  session      : SessionContract
  types        : Array StaticTypeDesc
  relations    : Array RelationDesc
  contractHash : ByteArray

structure ResolvedType where
  expected : StaticTypeDesc
  oid      : UInt32
  arrayOid : Option UInt32

structure ResolvedCatalog (db : DatabaseDesc) where
  types    : Array ResolvedType
  proof    : CatalogConforms db types

structure CheckedConnection (db : DatabaseDesc) where
  raw      : Pg.Connection
  catalog  : ResolvedCatalog db
```

### Connection attachment

Each generated database module exposes:

```lean
def AppDb.attach
    (conn : Pg.Connection) :
    Std.Async.Async
      (Except Pg.Typed.Error
        (Pg.Typed.CheckedConnection AppDb.database))
```

Attachment performs:

1. server-major validation;
2. session-setting validation or installation;
3. symbolic type resolution;
4. relevant catalog comparison;
5. construction of a `ResolvedCatalog` witness.

`CheckedConnection` is a capability proving that these executable checks succeeded against the catalog data that was read. It is not a claim that an external database can never change afterward.

### Per-query preparation

On first use of a generated query on a physical connection:

1. Resolve expected parameter `TypeKey`s to current OIDs.
2. Prepare the literal SQL using those OIDs.
3. Compare returned parameter count and types.
4. Compare result-column count, names, type keys, and type modifiers.
5. Cache the prepared statement under a name derived from its contract hash.

The query is executed only after this descriptor comparison succeeds.

Consequently, two separate drift checks exist:

* attachment checks the generated schema contract;
* statement preparation checks the exact runtime query contract.

Concurrent DDL or a changed `search_path` can therefore cause a typed `SchemaDrift` or `QueryDrift` error, but cannot silently decode a value into an incompatible Lean type.

### User-defined codecs

`PgEncode.typeOid` is suitable for fixed built-in types, but user-defined domains, enums, arrays, and extension types need runtime-resolved OIDs. Add a descriptor-oriented codec:

```lean
structure ResolvedCodec (α : Type) where
  expected : StaticTypeDesc
  encode   : ResolvedType → α →
             Except Pg.Typed.Error EncodedValue
  decode   : ResolvedType → UInt16 → Option ByteArray →
             Except Pg.Typed.Error α
```

Generated enum and domain wrappers receive `ResolvedCodec` values. Built-in codecs delegate to the existing `PgEncode` and `PgDecode` instances.

Unsupported extension types fail generation unless a declared type override supplies:

```text
Lean type
static TypeKey
codec target
optional refinement translator
```

---

## 8. PostgreSQL constraints as Lean propositions

This layer should follow the `protovalidate-lean` pattern exactly in one important respect: generated values carry proofs produced by an executable validator, rather than an opaque assertion that PostgreSQL checked them. `protovalidate-lean` generates a compositional `ValidPred`, a proof-producing `validate`, and soundness/completeness theorems. ([GitHub][13])

### 8.1 Typed constraint IR

Constraint expressions are not retained merely as SQL strings. The code generator translates the supported subset into a typed expression IR:

```lean
inductive SqlTruth
  | true
  | false
  | unknown

inductive ConstraintExpr (row : RowShape) : SqlType → Type
  | column
  | literal
  | isNull
  | isNotNull
  | eq
  | lt
  | le
  | and
  | or
  | not
  | add
  | sub
  | charLength
  | ...
```

The first supported subset should include:

* null tests;
* Boolean connectives;
* comparisons over supported exact scalar types;
* integer and exact numeric arithmetic where semantics are modeled;
* enum equality;
* character length;
* domain nesting;
* casts known to preserve modeled values.

Collation-sensitive text ordering, arbitrary user-defined functions, volatile expressions, locale-sensitive regular expressions, and unsupported extension operators are rejected for proposition generation unless an explicit translation plugin is provided.

The generator should use PostgreSQL's normalized constraint definition as its input and parse only this expression subset. PostgreSQL documentation recommends extracting check definitions rather than depending on the internal `pg_node_tree` representation. ([PostgreSQL][7])

This is an implementation parser inside the external generator, not a user-facing DDL grammar in Lean.

### 8.2 Three-valued check semantics

PostgreSQL considers a `CHECK` constraint satisfied when its expression evaluates to either true or null; only false violates the constraint. ([PostgreSQL][14])

Therefore the generated semantics must not translate nullable SQL expressions directly to ordinary Boolean conjunctions. Define:

```lean
def SqlTruth.checkPasses : SqlTruth → Prop
  | .false   => False
  | .true    => True
  | .unknown => True
```

For example:

```sql
age integer CHECK (age >= 0)
```

becomes:

```lean
match row.age with
| none   => True
| some n => 0 ≤ n
```

A separate `NOT NULL` constraint removes the `Option`.

### 8.3 Proof-producing validation

For every supported domain or row predicate, generate:

```lean
def ValidPred : Base → Prop

instance (x : Base) : Decidable (ValidPred x)

def validate :
  (x : Base) →
  Except Pg.ConstraintViolation { y : Base // ValidPred y }

theorem validate_sound :
  validate x = .ok y →
  y.val = x ∧ ValidPred x

theorem validate_complete :
  ValidPred x →
  ∃ y, validate x = .ok y
```

A result-row decoder first decodes `RowData`, then invokes `validate`, and returns the subtype only when it has constructed the proof.

This has an important consequence: the proof does not rely on an axiom saying “PostgreSQL obeys its constraints.” Even if the database has drifted, contains previously unvalidated data, or the query projects data through an unexpected path, a refined Lean value is produced only after its proposition has been decided on the decoded value.

### 8.4 Which constraints refine a value

Only **value-local** guarantees belong in a row subtype:

* not-null;
* enum membership;
* domain checks;
* type-modifier bounds;
* supported column checks;
* supported table checks over fields of the same row.

Primary-key uniqueness, unique constraints, foreign keys, and exclusion constraints are not predicates of one row. They quantify over a database state or relation. Encoding them as `{x // P x}` would be semantically wrong.

Their normalized future form should be:

```lean
def Users.PrimaryKeyUnique
    (state : AppDb.DatabaseState) : Prop := ...

def Orders.UserForeignKey
    (state : AppDb.DatabaseState) : Prop := ...
```

For a primary key, only the not-null component may refine an individual row; uniqueness remains relational.

Indexes similarly remain schema metadata unless they support a relational constraint.

### 8.5 Constraint propagation into query results

A query result receives a refinement only when it can be rechecked locally:

* An identity projection of a domain-valued column retains the domain subtype.
* A supported check on a directly projected field may be retained.
* A multi-column table check may be retained only when all referenced columns are identity projections from the same source row.
* A cast or expression loses the source refinement unless the generator has a declared preservation rule.
* A query predicate such as `WHERE age ≥ 18` may eventually refine the result only when the relevant value is projected and the predicate lies in the supported expression IR.

This provenance discipline prevents constraints from being propagated merely because a result column happens to have the same name or base SQL type.

---

## 9. Version and extension model

The normalized IR has version-specific probe adapters:

```text
Pg.Codegen.Probe.Pg17
Pg.Codegen.Probe.Pg18
```

Both produce the same `DatabaseIR`.

The canonical PostgreSQL major is part of the generated contract. The compatibility test runs the full migrations and queries on both versions and compares:

* generated Lean-level type mappings;
* query parameter types;
* result names and types;
* nullability classification;
* supported constraints;
* required extension versions.

A difference is either:

* accepted through an explicit compatibility override; or
* a failed compatibility test.

There should be no attempt to generate one API by taking the union of incompatible PostgreSQL-17 and PostgreSQL-18 behavior.

---

The code emitter should be pure:

```lean
def emitDatabase :
  DatabaseIR → Except CodegenError GeneratedSources
```

That enables golden tests without launching PostgreSQL. Integration tests separately establish that catalog probing and query description produce the expected IR.

---

## 11. Delivery sequence

### Milestone 1: checked query records

This is the minimum useful release.

It includes:

* hermetic PostgreSQL 18 DDL replay;
* PostgreSQL 17 compatibility target;
* canonical schema/query IR;
* schemas, tables, columns, indexes, enums, domains, and constraints in the IR;
* built-in `pg-lean` type mappings;
* enum generation;
* domain branding without full check-expression propositions;
* literal query files with generated `Params` and `Row`;
* conservative `Option` inference;
* `execute`, `exactlyOne`, `zeroOrOne`, and `many`;
* runtime symbolic OID resolution;
* `CheckedConnection`;
* runtime prepared-statement descriptor verification;
* type override hooks;
* hard errors for unsupported result types.

Acceptance criteria:

* Removing or changing a selected column breaks generated Lean consumers.
* Changing a parameter type fails generation or changes `Params`.
* A nullable result is never decoded into a plain field.
* User-defined OIDs are absent from generated source.
* Connecting to an incompatible deployment produces `SchemaDrift` before typed execution.
* Changing a query's runtime result descriptor produces `QueryDrift`.

### Milestone 2: local refinements

Add:

* typed constraint-expression IR;
* PostgreSQL three-valued semantics;
* domain and row `ValidPred`;
* proof-producing validators;
* soundness and completeness theorems;
* propagation through direct query projections;
* diagnostics for unsupported constraint constructs.

### Milestone 3: broader PostgreSQL types

Add:

* runtime-resolved one-dimensional arrays of generated types;
* composite-valued cells;
* ranges and multiranges;
* extension codec packages;
* view and table-valued-function metadata;
* richer type-modifier refinements.

`pg-lean` already supports text and binary codecs for the main built-in scalar types and one-dimensional arrays, so the first expansion should wrap that existing surface rather than replace it. ([GitHub][5])

### Milestone 4: relational propositions

Add a transaction- or snapshot-indexed logical model for:

* uniqueness;
* primary keys;
* foreign keys;
* exclusion constraints;
* mutation preconditions and postconditions.

This layer should not delay checked query records or local constraint subtypes.

---

## Locked architectural invariants

The design should retain the following invariants throughout implementation:

1. PostgreSQL, not a Lean DDL model, is the authority for SQL parsing, name resolution, casts, and query result types.
2. Normal Bazel builds are hermetic and do not require a network database.
3. Typed queries are declared literal source artifacts; dynamically constructed SQL remains untyped.
4. Generated contracts contain symbolic type identities, never installation-specific user OIDs.
5. Unknown result nullability becomes `Option`, not an optimistic plain type.
6. Runtime statement descriptors are checked before decoding.
7. Local propositions are accompanied by proof-producing validators.
8. Cross-row constraints are not misrepresented as predicates of an individual row.
9. No axiom or unchecked cast is used to turn an external database assertion into a Lean proof.
10. PostgreSQL 17 and 18 differences are normalized by versioned probe adapters and tested explicitly.

This architecture obtains the practical fidelity of jOOQ and SQLx, preserves the Bazel/codegen structure already established by `grpc-lean`, and reaches the proof-bearing subtype model of `protovalidate-lean` without maintaining a second PostgreSQL language implementation inside Lean.

[1]: https://raw.githubusercontent.com/pb64-lean/pg-lean/main/Pg/Connection.lean "https://raw.githubusercontent.com/pb64-lean/pg-lean/main/Pg/Connection.lean"
[2]: https://www.jooq.org/doc/latest/manual/getting-started/use-cases/jooq-as-a-sql-builder-with-code-generation/ "https://www.jooq.org/doc/latest/manual/getting-started/use-cases/jooq-as-a-sql-builder-with-code-generation/"
[3]: https://www.postgresql.org/docs/18/protocol-flow.html "https://www.postgresql.org/docs/18/protocol-flow.html"
[4]: https://raw.githubusercontent.com/pb64-lean/grpc-lean/main/proto.bzl "https://raw.githubusercontent.com/pb64-lean/grpc-lean/main/proto.bzl"
[5]: https://github.com/pb64-lean/pg-lean "GitHub - pb64-lean/pg-lean: PostgreSQL client in Lean 4: pure-Lean wire protocol, SCRAM auth, TLS, COPY, pipelining · GitHub"
[6]: https://www.postgresql.org/docs/18/catalog-pg-type.html "https://www.postgresql.org/docs/18/catalog-pg-type.html"
[7]: https://www.postgresql.org/docs/17/catalog-pg-constraint.html "https://www.postgresql.org/docs/17/catalog-pg-constraint.html"
[8]: https://www.postgresql.org/docs/current/datatype-oid.html "https://www.postgresql.org/docs/current/datatype-oid.html"
[9]: https://www.postgresql.org/docs/18/protocol-message-formats.html "https://www.postgresql.org/docs/18/protocol-message-formats.html"
[10]: https://raw.githubusercontent.com/launchbadge/sqlx/main/sqlx-postgres/src/connection/describe.rs "https://raw.githubusercontent.com/launchbadge/sqlx/main/sqlx-postgres/src/connection/describe.rs"
[11]: https://www.postgresql.org/docs/18/catalog-pg-proc.html "https://www.postgresql.org/docs/18/catalog-pg-proc.html"
[12]: https://raw.githubusercontent.com/pb64-lean/pg-lean/main/Pg/Types/Codec.lean "https://raw.githubusercontent.com/pb64-lean/pg-lean/main/Pg/Types/Codec.lean"
[13]: https://github.com/pb64-lean/protovalidate-lean "https://github.com/pb64-lean/protovalidate-lean"
[14]: https://www.postgresql.org/docs/18/ddl-constraints.html "https://www.postgresql.org/docs/18/ddl-constraints.html"

