import Pgx.Codegen.Emit

/-!
Pure golden, validation, and determinism tests for generated local refinements.
-/

namespace Pgx.Test.Emit

open Pgx
open Pgx.Codegen
open Pgx.Codegen.Identifier

private def base (name : String) : TypeRef :=
  { key := { schema := "pg_catalog", name, kind := .base } }

private def int4 : TypeRef := base "int4"
private def int8 : TypeRef := base "int8"
private def text : TypeRef := base "text"
private def bool : TypeRef := base "bool"
private def varchar12 : TypeRef :=
  { key := { schema := "pg_catalog", name := "varchar", kind := .base }, typmod := some 16 }

private def statusKey : TypeKey :=
  { schema := "app", name := "user_status", kind := .enum }

private def userIdKey : TypeKey :=
  { schema := "app", name := "user_id", kind := .domain }

private def emailKey : TypeKey :=
  { schema := "app", name := "email_address", kind := .domain }

private def reviewedStatusKey : TypeKey :=
  { schema := "app", name := "reviewed_status", kind := .domain }

private def ref (key : TypeKey) : TypeRef := { key }

private def usersKey : RelationKey := { schema := "app", name := "users" }

private def scalar (declared : TypeRef) (base : Pgx.Constraint.ScalarKind)
    (domains : Array TypeKey := #[]) : Pgx.Constraint.ScalarType :=
  { declared, base, domains }

private def emailScalar : Pgx.Constraint.ScalarType :=
  scalar (ref emailKey) .text #[emailKey]

private def userIdScalar : Pgx.Constraint.ScalarType :=
  scalar (ref userIdKey) .int64 #[userIdKey]

private def int4Scalar : Pgx.Constraint.ScalarType := scalar int4 .int32

private def emailConstraint : DomainConstraintIR := {
  name := "email_nonempty"
  source := "CHECK ((char_length(VALUE) > 0))"
  expression := .compare .gt
    (.cast .identity
      (.charLength (.domainValue emailScalar true) int4Scalar) int4Scalar)
    (.cast .identity (.literal (.integer 0) int4Scalar) int4Scalar)
}

private def userIdConstraint : DomainConstraintIR := {
  name := "user_id_positive"
  source := "CHECK ((VALUE > 0))"
  expression := .compare .gt
    (.cast .identity (.domainValue userIdScalar true) userIdScalar)
    (.cast .identity (.literal (.integer 0) userIdScalar) userIdScalar)
}

private def usersIdConstraint : ConstraintIR := {
  relation := usersKey
  name := "users_id_positive"
  kind := .check
  expression := some "CHECK ((id > 0))"
  localExpression := some <| .compare .gt
    (.cast .identity (.column "id" userIdScalar false) userIdScalar)
    (.cast .identity (.literal (.integer 0) userIdScalar) userIdScalar)
}

private def fixtureBase : DatabaseIR := {
  serverMajor := 18
  supportedServerMajors := #[18]
  serverFeatures := #["generated-columns", "identity-columns"]
  session := {
    searchPath := #["app", "pg_catalog"]
    timezone := "UTC"
    encoding := "UTF8"
  }
  schemas := #[{ name := "audit" }, { name := "app" }]
  enums := #[{
    key := statusKey
    -- The first two normalize identically; the generated cases must not.
    labels := #["new", "in_review", "in__review", "match", "βeta"]
  }]
  domains := #[
    { key := reviewedStatusKey, base := ref statusKey, notNull := true },
    { key := emailKey, base := text, notNull := true,
      constraints := #[emailConstraint.source],
      localConstraints := #[emailConstraint] },
    { key := userIdKey, base := int8, notNull := true,
      constraints := #[userIdConstraint.source],
      localConstraints := #[userIdConstraint] }
  ]
  relations := #[
    {
      key := { schema := "audit", name := "user_events" }
      kind := .table
      columns := #[
        { name := "payload", ordinal := 3, ty := text, nullable := true },
        { name := "user_id", ordinal := 1, ty := ref userIdKey, nullable := false },
        { name := "success", ordinal := 2, ty := bool, nullable := false }
      ]
    },
    {
      key := usersKey
      kind := .table
      columns := #[
        { name := "email", ordinal := 2, ty := ref emailKey, nullable := false },
        { name := "id", ordinal := 1, ty := ref userIdKey, nullable := false,
          identity := true },
        { name := "status", ordinal := 3, ty := ref reviewedStatusKey,
          nullable := false },
        { name := "nickname", ordinal := 4, ty := varchar12, nullable := true }
      ]
    }
  ]
  constraints := #[
    {
      relation := usersKey
      name := "users_pkey"
      kind := .primaryKey
      columns := #["id"]
    },
    {
      relation := usersKey
      name := "users_email_key"
      kind := .unique
      columns := #["email"]
    },
    usersIdConstraint
  ]
  indexes := #[{
    relation := usersKey
    name := "users_email_key"
    unique := true
    primary := false
    valid := true
    columns := #["email"]
  }]
  queries := #[
    {
      name := "ListUsers"
      sql := "SELECT id, email, status FROM app.users ORDER BY id"
      sqlHash := "list-users-v1"
      params := #[]
      columns := #[
        { name := "id", ty := int8, logicalType := some (ref userIdKey), nullable := false,
          origin := some { relation := usersKey, name := "id" } },
        { name := "email", ty := text, logicalType := some (ref emailKey), nullable := true,
          origin := some { relation := usersKey, name := "email" } },
        { name := "status", ty := ref statusKey,
          logicalType := some (ref reviewedStatusKey), nullable := false,
          origin := some { relation := usersKey, name := "status" } }
      ]
      cardinality := .many
    },
    {
      name := "DeleteUser"
      sql := "DELETE FROM app.users WHERE id = $1"
      sqlHash := "delete-user-v1"
      params := #[{ position := 1, name := "id", ty := ref userIdKey, nullable := false }]
      columns := #[]
      cardinality := .execute
    },
    {
      name := "GetUser"
      sql := "SELECT id, email, status\nFROM app.users WHERE id = $1 /* \"checked\" */"
      sqlHash := "get-user-v1"
      params := #[{ position := 1, name := "id", ty := ref userIdKey, nullable := false }]
      columns := #[
        { name := "id", ty := int8, logicalType := some (ref userIdKey), nullable := false,
          origin := some { relation := usersKey, name := "id" } },
        { name := "email", ty := text, logicalType := some (ref emailKey), nullable := false,
          origin := some { relation := usersKey, name := "email" } },
        { name := "status", ty := ref statusKey,
          logicalType := some (ref reviewedStatusKey), nullable := false,
          origin := some { relation := usersKey, name := "status" } }
      ]
      cardinality := .zeroOrOne
    },
    {
      name := "CountUsers"
      sql := "SELECT count(*) AS count FROM app.users"
      sqlHash := "count-users-v1"
      params := #[]
      columns := #[{ name := "count", ty := int8, nullable := false }]
      cardinality := .exactlyOne
    }
  ]
  typeOverrides := #[
    {
      key := { schema := "ext", name := "citext", kind := .base }
      leanType := "String"
      codec := "External.citextCodec"
      importModule := some "Pg.Types.Codec"
    },
    {
      key := { schema := "ext", name := "vector", kind := .base }
      leanType := "External.Vector"
      codec := "External.vectorCodec"
      importModule := some "Pg.Types.Codec"
    }
  ]
}

/-- Public only so the generated modules can be materialized by a smoke-test
driver without duplicating this fairly complete fixture. -/
def fixture : DatabaseIR := Pgx.Codegen.Projection.planDatabase fixtureBase

private def shuffled : DatabaseIR := {
  fixture with
  supportedServerMajors := fixture.supportedServerMajors.reverse
  serverFeatures := fixture.serverFeatures.reverse
  schemas := fixture.schemas.reverse
  enums := fixture.enums.reverse
  domains := fixture.domains.reverse.map fun value =>
    { value with constraints := value.constraints.reverse }
  relations := fixture.relations.reverse.map fun value =>
    { value with columns := value.columns.reverse }
  constraints := fixture.constraints.reverse
  indexes := fixture.indexes.reverse
  queries := fixture.queries.reverse.map fun value =>
    { value with params := value.params.reverse }
  typeOverrides := fixture.typeOverrides.reverse
}

private def generated : Except CodegenError GeneratedSources :=
  emitDatabase "app_db" fixture

private def unsupported : DatabaseIR := {
  fixture with
  queries := fixture.queries.map fun query =>
    if query.name == "GetUser" then
      { query with params := query.params.map fun param => {
          param with
          ty := { key := { schema := "pg_catalog", name := "int4", kind := .array } }
        } }
    else query
}

private def withImportModule (moduleName : String) : DatabaseIR := {
  fixture with
  typeOverrides := fixture.typeOverrides.map fun value =>
    { value with importModule := some moduleName }
}

private def forgedDomainAst : DatabaseIR := {
  fixture with
  domains := fixture.domains.map fun domain =>
    if domain.key == emailKey then
      { domain with localConstraints := domain.localConstraints.map fun constraint =>
          { constraint with expression := .constant (some true) } }
    else domain
}

private def forgedQueryPlan : DatabaseIR := {
  fixture with
  queries := fixture.queries.map fun query =>
    if query.name == "GetUser" then { query with localConstraints := #[] } else query
}

private def forgedLogicalWire : DatabaseIR := {
  fixture with
  queries := fixture.queries.map fun query =>
    if query.name == "GetUser" then
      { query with columns := query.columns.map fun column =>
          if column.name == "email" then { column with ty := int8 } else column }
    else query
}

private def invalidCharacterTypmod : DatabaseIR := {
  fixture with
  relations := fixture.relations.map fun relation =>
    if relation.key == usersKey then
      { relation with columns := relation.columns.map fun column =>
          if column.name == "nickname" then
            { column with ty := { column.ty with typmod := some 4 } }
          else column }
    else relation
}

private def constrainedOverride : DatabaseIR := {
  fixture with
  queries := #[]
  typeOverrides := fixture.typeOverrides.push {
    key := emailKey
    leanType := "String"
    codec := "External.citextCodec"
    importModule := some "Pg.Types.Codec"
  }
}

private def typmodOverride : DatabaseIR := {
  fixture with
  typeOverrides := fixture.typeOverrides.push {
    key := varchar12.key
    leanType := "String"
    codec := "External.citextCodec"
    importModule := some "Pg.Types.Codec"
  }
}

private def expectedRoot : String :=
  "/- This file is generated by lean-pgx.  Do not edit it directly. -/\n" ++
  "import AppDb.Types\n" ++
  "import AppDb.Schema\n" ++
  "import AppDb.Constraints\n" ++
  "import AppDb.Queries.CountUsers\n" ++
  "import AppDb.Queries.DeleteUser\n" ++
  "import AppDb.Queries.GetUser\n" ++
  "import AppDb.Queries.ListUsers\n"

private def isUnsupported (result : Except CodegenError GeneratedSources) : Bool :=
  match result with
  | .error (.unsupportedType key _) => key.kind == .array
  | _ => false

private def isError (result : Except CodegenError GeneratedSources) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

def main : IO UInt32 := do
  -- Identifier golden: keywords, punctuation, Unicode, and scoped collisions.
  assert! upperCamel "9 bad/name" == "n9U32BadU47Name"
  assert! lowerCamel "match" == "match_value"
  assert! lowerCamel "βeta" == "u946Eta"
  let (first, scope) := (Scope.mk #["inReview"]).claim "inReview"
  let (second, _) := scope.claim "inReview"
  assert! first == "inReview_2"
  assert! second == "inReview_3"
  assert! stringLiteral "line\n\"quote\"\\tail" == "\"line\\n\\\"quote\\\"\\\\tail\""

  let sources ← match generated with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  let reordered ← match emitDatabase "app_db" shuffled with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  let legacySources ← match emitDatabase "app_db"
      { fixture with supportedServerMajors := #[] } with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))

  -- Fixed output layout and a compact full-file golden for the root module.
  assert! sources.modulePrefix == "AppDb"
  assert! sources.all.map (·.path) == #[
    "AppDb/Types.lean",
    "AppDb/Schema.lean",
    "AppDb/Constraints.lean",
    "AppDb/Queries/CountUsers.lean",
    "AppDb/Queries/DeleteUser.lean",
    "AppDb/Queries/GetUser.lean",
    "AppDb/Queries/ListUsers.lean",
    "AppDb.lean"
  ]
  assert! sources.root.contents == expectedRoot

  -- Stable emission follows semantic IR normalization.
  assert! sources == reordered
  assert! match emitDatabase "app_db" fixture, generated with
    | .ok left, .ok right => left == right
    | .error left, .error right => left == right
    | _, _ => false

  -- Generated API surface and collision-safe enum names.
  assert! sources.types.contents.contains "inductive AppUserStatus where"
  assert! sources.types.contents.startsWith
    ("/- This file is generated by lean-pgx.  Do not edit it directly. -/\n" ++
      "import Pg.Types.Codec\nimport Pgx.Constraint.Semantics\nimport Pgx.Typed\n")
  assert! (sources.types.contents.splitOn "import Pg.Types.Codec").length == 2
  assert! sources.types.contents.contains "| inReview"
  assert! sources.types.contents.contains "| inReview_2"
  assert! sources.types.contents.contains "| match_value"
  assert! sources.types.contents.contains "namespace AppEmailAddress\n\nstructure Data where"
  assert! sources.types.contents.contains "def ValidPred (value : Data) : Prop"
  assert! sources.types.contents.contains "abbrev Value := { value : Data // ValidPred value }"
  assert! sources.types.contents.contains "def validate (value : Data) : Except Pgx.ConstraintViolation Value"
  assert! sources.types.contents.contains "theorem validate_sound"
  assert! sources.types.contents.contains "theorem validate_complete"
  assert! sources.types.contents.contains "def codec : Pgx.Typed.ResolvedCodec Value"
  assert! sources.types.contents.contains "Pgx.Typed.Error.constraintViolation violation"
  assert! sources.types.contents.contains
    "abbrev AppEmailAddress := AppEmailAddress.Value"
  assert! sources.schema.contents.contains "def database : Pgx.Typed.DatabaseDesc"
  assert! sources.schema.contents.contains "serverMajors := #[18]"
  assert! !(sources.schema.contents.contains "serverMajors := #[17, 18]")
  assert! legacySources.schema.contents.contains "serverMajors := #[18]"
  assert! sources.schema.contents.contains "def attach (conn : Pg.Connection)"
  assert! sources.schema.contents.contains "abbrev Row := { value : Data // ValidPred value }"
  assert! sources.schema.contents.contains "users_id_positive"
  assert! sources.schema.contents.contains "Pgx.Constraint.evaluateCharacterTypmod (some (16))"
  assert! !(sources.schema.contents.contains "users_pkey")
  assert! !(sources.schema.contents.contains "users_email_key")
  assert! sources.constraints.contents.contains "def indexes : Array Pgx.IndexIR"
  assert! sources.constraints.contents.contains "localExpression := some ("
  assert! sources.queries.any (fun source =>
    source.contents.contains "Pgx.Typed.fetchOptional spec conn params")
  assert! sources.queries.any (fun source =>
    source.contents.contains "Pgx.Typed.execute spec conn params")
  assert! sources.queries.any (fun source =>
    source.contents.contains "Pgx.Typed.fetchOne spec conn params")
  assert! sources.queries.any (fun source =>
    source.contents.contains "Pgx.Typed.fetchMany spec conn params")
  assert! sources.queries.any (fun source =>
    source.contents.contains "sql := \"SELECT id, email, status\\nFROM app.users WHERE id = $1 /* \\\"checked\\\" */\"")
  let some getUser := sources.findModule? "AppDb.Queries.GetUser"
    | throw (IO.userError "missing generated GetUser module")
  assert! getUser.contents.contains "structure RowData where"
  assert! getUser.contents.contains "email : AppDb.Types.AppEmailAddress"
  assert! getUser.contents.contains "abbrev Row := { value : RowData // ValidPred value }"
  assert! getUser.contents.contains "AppDb.Types.AppEmailAddress.validate { toBase := decodedWire1 }"
  assert! !(getUser.contents.contains
    "decodeResolved AppDb.Types.AppEmailAddress.codec")
  assert! getUser.contents.contains "users_id_positive"
  assert! getUser.contents.contains "match validate rowData with"
  assert! getUser.contents.contains "Pgx.Typed.Error.constraintViolation violation"
  let some listUsers := sources.findModule? "AppDb.Queries.ListUsers"
    | throw (IO.userError "missing generated ListUsers module")
  assert! listUsers.contents.contains "email : Option (AppDb.Types.AppEmailAddress)"
  assert! listUsers.contents.contains "| none => pure none"
  assert! listUsers.contents.contains "| some present => some <$> (do"

  -- Source contracts remain symbolic and unsupported types are hard errors.
  for source in sources.all do
    assert! !(source.contents.contains "90001")
  assert! isUnsupported (emitDatabase "AppDb" unsupported)
  assert! isError (emitDatabase "AppDb" (withImportModule ""))
  assert! isError (emitDatabase "AppDb" (withImportModule " Pg.Types.Codec"))
  assert! isError (emitDatabase "AppDb" forgedDomainAst)
  assert! isError (emitDatabase "AppDb" forgedQueryPlan)
  assert! isError (emitDatabase "AppDb" forgedLogicalWire)
  assert! isError (emitDatabase "AppDb" invalidCharacterTypmod)
  assert! isError (emitDatabase "AppDb" constrainedOverride)
  assert! isError (emitDatabase "AppDb" typmodOverride)
  return 0

end Pgx.Test.Emit

def main : IO UInt32 :=
  Pgx.Test.Emit.main
