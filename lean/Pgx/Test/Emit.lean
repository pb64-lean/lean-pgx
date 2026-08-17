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

private def int2 : TypeRef := base "int2"
private def int4 : TypeRef := base "int4"
private def int8 : TypeRef := base "int8"
private def text : TypeRef := base "text"
private def bool : TypeRef := base "bool"
private def time : TypeRef := base "time"
private def citext : TypeRef :=
  { key := { schema := "ext", name := "citext", kind := .base } }
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

private def emailPresentConstraint : DomainConstraintIR := {
  name := "email_present"
  source := "CHECK ((VALUE IS NOT NULL))"
  expression := .isNotNull (.domainValue emailScalar true)
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
    { key := emailKey, base := text, notNull := false,
      constraints := #[emailPresentConstraint.source, emailConstraint.source],
      localConstraints := #[emailPresentConstraint, emailConstraint] },
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
      rowPreservedRelations := #[usersKey]
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
      rowPreservedRelations := #[usersKey]
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

private def binaryFormatFixture : DatabaseIR := {
  fixture with
  queries := fixture.queries.push {
    name := "MixedFormats"
    sql := "SELECT $1::int4 AS count, label::ext.citext FROM app.labels WHERE rank = $2"
    sqlHash := "mixed-formats-v1"
    params := #[
      { position := 1, name := "count", ty := int4, nullable := true },
      { position := 2, name := "rank", ty := int2, nullable := false }
    ]
    columns := #[
      { name := "count", ty := int4, nullable := false },
      { name := "label", ty := citext, nullable := false }
    ]
    cardinality := .many
  }
}

private def int8Scalar : Pgx.Constraint.ScalarType := scalar int8 .int64

private def reversedUsersIdConstraint : ConstraintIR := {
  relation := usersKey
  name := "users_id_positive_reversed"
  kind := .check
  expression := some "CHECK ((0 < id))"
  localExpression := some <| .compare .lt
    (.cast .integerWiden (.literal (.integer 0) int4Scalar) userIdScalar)
    (.cast .identity (.column "id" userIdScalar false) userIdScalar)
}

private def contradictoryUsersIdConstraint : ConstraintIR := {
  relation := usersKey
  name := "users_id_contradictory"
  kind := .check
  expression := some "CHECK ((id >= 10) AND (id < 5))"
  localExpression := some <| .and
    (.compare .ge
      (.cast .identity (.column "id" userIdScalar false) userIdScalar)
      (.cast .identity (.literal (.integer 10) userIdScalar) userIdScalar))
    (.compare .lt
      (.cast .identity (.column "id" userIdScalar false) userIdScalar)
      (.cast .identity (.literal (.integer 5) userIdScalar) userIdScalar))
}

private def nullableScoreConstraint : ConstraintIR := {
  relation := usersKey
  name := "users_score_range"
  kind := .check
  expression := some "CHECK ((score >= 0) AND (score < 100))"
  localExpression := some <| .and
    (.compare .ge
      (.cast .identity (.column "score" int8Scalar true) int8Scalar)
      (.cast .identity (.literal (.integer 0) int8Scalar) int8Scalar))
    (.compare .lt
      (.cast .identity (.column "score" int8Scalar true) int8Scalar)
      (.cast .identity (.literal (.integer 100) int8Scalar) int8Scalar))
}

private def quantityUInt32Constraint : ConstraintIR := {
  relation := usersKey
  name := "users_quantity_uint32"
  kind := .check
  expression := some
    "CHECK ((quantity >= 0) AND (quantity < '4294967296'::bigint))"
  localExpression := some <| .and
    (.compare .ge
      (.cast .identity (.column "quantity" int8Scalar false) int8Scalar)
      (.cast .identity (.literal (.integer 0) int8Scalar) int8Scalar))
    (.compare .lt
      (.cast .identity (.column "quantity" int8Scalar false) int8Scalar)
      (.cast .identity (.literal (.integer 4294967296) int8Scalar) int8Scalar))
}

private def rangeSpecializationFixture : DatabaseIR :=
  Pgx.Codegen.Projection.planDatabase {
    fixtureBase with
    relations := fixtureBase.relations.map fun relation =>
      if relation.key == usersKey then
        { relation with columns := relation.columns ++ #[
            { name := "score", ordinal := 5, ty := int8, nullable := true },
            { name := "quantity", ordinal := 6, ty := int8, nullable := false }
          ] }
      else relation
    constraints := fixtureBase.constraints ++ #[
      reversedUsersIdConstraint,
      contradictoryUsersIdConstraint,
      nullableScoreConstraint,
      quantityUInt32Constraint
    ]
  }

private def unsupportedRelationalFixture : DatabaseIR := {
  fixture with
  constraints := fixture.constraints.push {
    relation := usersKey
    name := "users_parent_partial_fk"
    kind := .foreignKey
    columns := #["id"]
    referencedRelation := some usersKey
    referencedColumns := #["id"]
    foreignKeyMatch := .partialMatch
  }
}

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

private def forgedDomainValidation : DatabaseIR := {
  fixture with
  domains := fixture.domains.map fun domain =>
    if domain.key == emailKey then
      { domain with localConstraints := domain.localConstraints.map fun constraint =>
          { constraint with validated := false } }
    else domain
}

private def forgedRelationValidation : DatabaseIR := {
  fixture with
  constraints := fixture.constraints.map fun constraint =>
    if constraint.name == usersIdConstraint.name then
      { constraint with validated := false }
    else constraint
}

private def forgedQueryPlan : DatabaseIR := {
  fixture with
  queries := fixture.queries.map fun query =>
    if query.name == "GetUser" then { query with localConstraints := #[] } else query
}

private def forgedRowPreservedRelation : DatabaseIR := {
  fixture with
  queries := fixture.queries.map fun query =>
    if query.name == "GetUser" then
      { query with rowPreservedRelations := #[{ schema := "app", name := "missing" }] }
    else query
}

private def forgedRowPreservedWidening : DatabaseIR := {
  fixture with
  queries := fixture.queries.map fun query =>
    if query.name == "GetUser" then
      { query with columns := query.columns.map fun column =>
          if column.name == "id" then
            { column with nullable := true, nullWidened := true }
          else column }
    else query
}

private def forgedRowPreservedWithoutOrigin : DatabaseIR := {
  fixture with
  queries := fixture.queries.map fun query =>
    if query.name == "CountUsers" then
      { query with rowPreservedRelations := #[usersKey] }
    else query
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

private def statusArrayKey : TypeKey :=
  { schema := "app", name := "status_vector", kind := .array }

private def varcharArrayKey : TypeKey :=
  { schema := "pg_catalog", name := "_varchar", kind := .array }

private def timeArrayKey : TypeKey :=
  { schema := "pg_catalog", name := "_time", kind := .array }

private def emailArrayKey : TypeKey :=
  { schema := "app", name := "email_vector", kind := .array }

private def automaticStatusArrayKey : TypeKey :=
  { schema := "app", name := "_user_status", kind := .array }

private def varcharArray12 : TypeRef :=
  { key := varcharArrayKey, typmod := some 16 }

private def statusListKey : TypeKey :=
  { schema := "app", name := "status_list", kind := .domain }

private def packetKey : TypeKey :=
  { schema := "app", name := "review_packet", kind := .composite }

private def scoreRangeKey : TypeKey :=
  { schema := "app", name := "score_range", kind := .range }

private def scoreMultirangeKey : TypeKey :=
  { schema := "app", name := "score_multirange", kind := .multirange }

private def activePacketsKey : RelationKey :=
  { schema := "app", name := "active_packets" }

/-- One compact contract exercising every generated PostgreSQL type shape,
including a domain whose base is itself a generated container. -/
private def generatedTypeFixture : DatabaseIR := {
  fixture with
  arrays := #[
    { key := automaticStatusArrayKey, element := ref statusKey },
    { key := statusArrayKey, element := ref statusKey },
    { key := varcharArrayKey, element := base "varchar" },
    { key := timeArrayKey, element := time },
    { key := emailArrayKey, element := ref emailKey }
  ]
  domains := fixture.domains.push {
    key := statusListKey
    base := ref statusArrayKey
    notNull := true
  }
  composites := #[{
    key := packetKey
    fields := #[
      { name := "statuses", ordinal := 1, ty := ref statusListKey },
      { name := "score", ordinal := 2, ty := ref scoreRangeKey },
      { name := "title", ordinal := 3, ty := varchar12 },
      { name := "observed_at", ordinal := 4, ty := time },
      { name := "tags", ordinal := 5, ty := varcharArray12 },
      { name := "email", ordinal := 6, ty := ref emailKey },
      { name := "times", ordinal := 7, ty := ref timeArrayKey }
    ]
  }]
  ranges := #[{
    key := scoreRangeKey
    subtype := time
    multirange := scoreMultirangeKey
    subtypeOpclass := { schema := "pg_catalog", name := "time_ops" }
    canonical := some {
      schema := "app"
      name := "score_range_canonical"
      inputTypes := #[ref scoreRangeKey]
    }
    subtypeDiff := some {
      schema := "app"
      name := "time_subtype_diff"
      inputTypes := #[time, time]
    }
  }]
  multiranges := #[{
    key := scoreMultirangeKey
    range := scoreRangeKey
  }]
  relations := fixture.relations.push {
    key := activePacketsKey
    kind := .view
    columns := #[
      { name := "packet", ordinal := 1, ty := ref packetKey, nullable := false },
      { name := "scores", ordinal := 2, ty := ref scoreMultirangeKey,
        nullable := true }
    ]
  }
  views := #[{
    relation := activePacketsKey
    definition := "SELECT packet, scores FROM app.review_queue WHERE active"
    checkOption := .local
    securityBarrier := true
  }]
  routines := #[{
    key := {
      schema := "app"
      name := "find_packets"
      inputTypes := #[ref statusListKey]
    }
    kind := .function
    args := #[
      { name := some "statuses", mode := .input, ty := ref statusListKey },
      { name := some "packet", mode := .table, ty := ref packetKey },
      { name := some "scores", mode := .table, ty := ref scoreMultirangeKey }
    ]
    returnsSet := true
    resultColumns := #[
      { name := "packet", ordinal := 1, ty := ref packetKey },
      { name := "scores", ordinal := 2, ty := ref scoreMultirangeKey }
    ]
    volatility := "s"
    parallel := "s"
  }]
}

private def invalidArrayDelimiter : DatabaseIR := {
  generatedTypeFixture with
  arrays := generatedTypeFixture.arrays.map fun value =>
    if value.key == statusArrayKey then { value with delimiter := ";" } else value
}

private def invalidRangeLink : DatabaseIR := {
  generatedTypeFixture with
  multiranges := generatedTypeFixture.multiranges.map fun value =>
    if value.key == scoreMultirangeKey then
      { value with range := { schema := "app", name := "other_range", kind := .range } }
    else value
}

private def invalidCompositeArity : DatabaseIR := {
  generatedTypeFixture with
  composites := generatedTypeFixture.composites.map fun value =>
    if value.key == packetKey then
      { value with fields := value.fields.map fun field =>
          if field.name == "score" then { field with ordinal := 3 } else field }
    else value
}

private def expectedRoot : String :=
  "module\n\n" ++
  "/- This file is generated by lean-pgx.  Do not edit it directly. -/\n" ++
  "public import AppDb.Types\n" ++
  "public import AppDb.Schema\n" ++
  "public import AppDb.Constraints\n" ++
  "public import AppDb.Queries.CountUsers\n" ++
  "public import AppDb.Queries.DeleteUser\n" ++
  "public import AppDb.Queries.GetUser\n" ++
  "public import AppDb.Queries.ListUsers\n\n" ++
  "public section\n\n"

private def isUnsupported (result : Except CodegenError GeneratedSources) : Bool :=
  match result with
  | .error (.unsupportedType key _) => key.kind == .array
  | _ => false

private def isError (result : Except CodegenError GeneratedSources) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

private def generatedTypeTests : IO Unit := do
  let sources ← match emitDatabase "type_shape_db" generatedTypeFixture with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))

  -- Generated container/composite types retain symbolic component
  -- descriptors and use the resolver-aware text and binary codec paths.
  assert! sources.types.contents.contains "namespace AppUserStatusArray"
  assert! !sources.types.contents.contains "namespace AppUserStatus_2"
  assert! sources.types.contents.contains "namespace AppStatusVector"
  assert! sources.types.contents.contains
    "abbrev Value := Pgx.Typed.PgArray (TypeShapeDb.Types.AppUserStatus)"
  assert! sources.types.contents.contains "arrayDelimiter := some (\",\")"
  assert! sources.types.contents.contains "Pgx.Typed.decodeArrayBinary element.oid"
  assert! sources.types.contents.contains "namespace AppEmailVector"
  assert! sources.types.contents.contains
    "abbrev Data := Pgx.Typed.PgArray (TypeShapeDb.Types.AppEmailAddress)"
  assert! sources.types.contents.contains "arrayElementsNotNull value"
  assert! sources.types.contents.contains "namespace AppStatusList"
  assert! sources.types.contents.contains "toBase : TypeShapeDb.Types.AppStatusVector"
  assert! sources.types.contents.contains "namespace AppReviewPacket"
  assert! sources.types.contents.contains
    "statuses : Option (TypeShapeDb.Types.AppStatusList)"
  assert! sources.types.contents.contains "score : Option (TypeShapeDb.Types.AppScoreRange)"
  assert! sources.types.contents.contains "title : Option (String)"
  assert! sources.types.contents.contains "observedAt : Option (Std.Time.PlainTime)"
  assert! sources.types.contents.contains
    "tags : Option (TypeShapeDb.Types.PgCatalogVarchar)"
  assert! sources.types.contents.contains
    "email : Option (TypeShapeDb.Types.AppEmailAddress)"
  assert! sources.types.contents.contains
    "times : Option (TypeShapeDb.Types.PgCatalogTime)"
  assert! sources.types.contents.contains
    "evaluateCharacterTypmod (some (16)) (value.title)"
  assert! sources.types.contents.contains "evaluateTimeTypmod (none)"
  assert! sources.types.contents.contains
    "evaluateArrayElements (fun item => Pgx.Constraint.evaluateCharacterTypmod (some (16)) (item))"
  assert! sources.types.contents.contains
    "evaluateArrayElements (fun item => Pgx.Constraint.evaluateTimeTypmod (none)"
  assert! sources.types.contents.contains
    "SqlTruth.isNotNull value.email"
  assert! sources.types.contents.contains "match value.val.statuses with"
  assert! sources.types.contents.contains "match validate decoded with"
  assert! sources.types.contents.contains "compositeFields := #["
  assert! sources.types.contents.contains "Pgx.Typed.renderCompositeText"
  assert! sources.types.contents.contains "Pgx.Typed.parseCompositeTextArity 7"
  assert! sources.types.contents.contains
    "abbrev Data := Pgx.Typed.PgRange (Std.Time.PlainTime)"
  assert! sources.types.contents.contains
    "evaluateRangeBounds (fun item => Pgx.Constraint.evaluateTimeTypmod (none)"
  assert! sources.types.contents.contains "rangeMultirange := some ("
  assert! sources.types.contents.contains "rangeCollation := none"
  assert! sources.types.contents.contains "rangeSubtypeOpclass := some ("
  assert! sources.types.contents.contains "name := \"time_ops\""
  assert! sources.types.contents.contains "rangeCanonical := some ("
  assert! sources.types.contents.contains "name := \"score_range_canonical\""
  assert! sources.types.contents.contains "rangeSubtypeDiff := some ("
  assert! sources.types.contents.contains "name := \"time_subtype_diff\""
  assert! sources.types.contents.contains "Pgx.Typed.decodeRangeBinary subtype.oid"
  assert! sources.types.contents.contains
    "abbrev Data := Pgx.Typed.PgMultirange (Std.Time.PlainTime)"
  assert! sources.types.contents.contains
    "evaluateMultirangeBounds (fun item => Pgx.Constraint.evaluateTimeTypmod (none)"
  assert! sources.types.contents.contains "multirangeRange := some ("
  assert! sources.types.contents.contains "Pgx.Typed.decodeMultirangeBinary subtype.oid"

  -- Views remain relation-shaped in Schema while semantic view and
  -- table-valued-function metadata is preserved verbatim in Constraints.
  assert! sources.schema.contents.contains
    "namespace TypeShapeDb.Schema.App.ActivePackets"
  assert! sources.schema.contents.contains
    "packet : TypeShapeDb.Types.AppReviewPacket"
  assert! sources.constraints.contents.contains "def views : Array Pgx.ViewIR"
  assert! sources.constraints.contents.contains
    "SELECT packet, scores FROM app.review_queue WHERE active"
  assert! sources.constraints.contents.contains "checkOption := .local"
  assert! sources.constraints.contents.contains "securityBarrier := true"
  assert! sources.constraints.contents.contains "def routines : Array Pgx.RoutineIR"
  assert! sources.constraints.contents.contains "name := \"find_packets\""
  assert! sources.constraints.contents.contains "returnsSet := true"
  assert! sources.constraints.contents.contains
    "name := \"scores\", ordinal := 2"

  assert! isError (emitDatabase "TypeShapeDb" invalidArrayDelimiter)
  assert! isError (emitDatabase "TypeShapeDb" invalidRangeLink)
  assert! isError (emitDatabase "TypeShapeDb" invalidCompositeArity)

-- This single golden test intentionally checks the complete generated surface.
-- Keep its elaboration budget local rather than raising it for the library.
set_option maxRecDepth 4096 in
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
  let unsupportedRelationalSources ←
      match emitDatabase "app_db" unsupportedRelationalFixture with
      | .ok value => pure value
      | .error error => throw (IO.userError (toString error))
  let binaryFormatSources ← match emitDatabase "app_db" binaryFormatFixture with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  let rangeSources ← match emitDatabase "range_db" rangeSpecializationFixture with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  generatedTypeTests

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
    ("module\n\n" ++
      "/- This file is generated by lean-pgx.  Do not edit it directly. -/\n" ++
      "public import Pg.Types.Codec\n" ++
      "public import Pgx.Constraint.Semantics\n" ++
      "public import Pgx.Typed\n\npublic section\n")
  assert! (sources.types.contents.splitOn "public import Pg.Types.Codec").length == 2
  for source in sources.all do
    assert! source.contents.startsWith "module\n\n"
    assert! source.contents.contains "\npublic section\n"
    assert! (source.contents.splitOn "\n").all (fun line => !line.startsWith "import ")
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
  assert! sources.schema.contents.contains "users_pkey"
  assert! sources.schema.contents.contains "users_email_key"
  assert! sources.schema.contents.contains "constraints := #["
  assert! sources.schema.contents.contains "indexes := #["
  assert! sources.constraints.contents.contains "def indexes : Array Pgx.IndexIR"
  assert! sources.constraints.contents.contains "localExpression := some ("
  assert! sources.constraints.contents.contains "inductive Table where"
  assert! sources.constraints.contents.contains "@[expose] def Row : Table → Type"
  assert! sources.constraints.contents.contains "@[expose] def schema : Pgx.Logic.Schema"
  assert! sources.constraints.contents.contains "| auditUserEvents"
  assert! sources.constraints.contents.contains "| appUsers"
  assert! sources.constraints.contents.contains
    "abbrev At (state : State) := Pgx.Logic.RowAt state .appUsers"
  assert! sources.constraints.contents.contains
    "namespace AppUsersUsersEmailKey"
  assert! sources.constraints.contents.contains "structure Key where"
  assert! sources.constraints.contents.contains
    "Pgx.Logic.Constraint.Unique state .appUsers"
  assert! sources.constraints.contents.contains
    "Pgx.Logic.Constraint.PrimaryKey state .appUsers"
  assert! sources.constraints.contents.contains "structure Semantics where"
  assert! sources.constraints.contents.contains "structure IntegrityContext"
  assert! sources.constraints.contents.contains "def modeledConstraints"
  assert! sources.constraints.contents.contains "def unsupportedRelationalConstraints"
  assert! unsupportedRelationalSources.constraints.contents.contains
    "def unsupportedRelationalConstraints : Array (Pgx.ConstraintKey × String) :=\n  #[({ relation := { schema := \"app\", name := \"users\" }, name := \"users_parent_partial_fk\" }, \"MATCH PARTIAL semantics are not supported\")]"
  assert! !(unsupportedRelationalSources.constraints.contents.contains
    "namespace AppUsersUsersParentPartialFk")
  assert! !(unsupportedRelationalSources.constraints.contents.contains
    "AppUsersUsersParentPartialFk.Holds")
  assert! sources.constraints.contents.contains "def insertSpec"
  assert! sources.constraints.contents.contains "def deleteSpec"
  assert! sources.constraints.contents.contains "def updateSpec"
  assert! sources.constraints.contents.contains
    "Live execution never manufactures one."
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
  let getUserSql :=
    "SELECT id, email, status\nFROM app.users WHERE id = $1 /* \"checked\" */"
  let getUserCacheKey :=
    Pgx.Typed.queryCacheKey fixture.contractHash "get-user-v1" getUserSql
  assert! getUserCacheKey.length == 64
  assert! getUser.contents.contains s!"cacheKey := \"{getUserCacheKey}\""
  assert! !(getUser.contents.contains "Pgx.Typed.queryCacheKey")
  -- The exact int8 wire result opts into binary, while the domain parameter
  -- and text/custom result codecs remain on their declared text path.
  assert! getUser.contents.contains "resultFormats := #[1, 0, 0]"
  assert! getUser.contents.contains "preparedEncode := some encodePreparedParams"
  assert! getUser.contents.contains "preparedDecode := some decodePreparedRow"
  assert! getUser.contents.contains "preparedSpanDecode := some decodePreparedSpanRow"
  assert! getUser.contents.contains
    "(values : Pg.Protocol.DataRowSpans) : Except Pgx.Typed.Error Row"
  assert! getUser.contents.contains
    "Pgx.Typed.decodePlannedBuiltin columns[0]!.typeOid columns[0]!.format values[0]!"
  assert! getUser.contents.contains
    "Pgx.Typed.decodePlannedBuiltinSpan columns[0]!.typeOid columns[0]!.format values 0"
  assert! !(getUser.contents.contains "Pg.binaryInt64 params.id")
  assert! getUser.contents.contains "structure RowData where"
  assert! getUser.contents.contains "email : AppDb.Types.AppEmailAddress"
  assert! getUser.contents.contains "abbrev Row := { value : RowData // ValidPred value }"
  assert! getUser.contents.contains "AppDb.Types.AppEmailAddress.validate { toBase := decodedWire1 }"
  assert! !(getUser.contents.contains
    "decodeResolved AppDb.Types.AppEmailAddress.codec")
  assert! getUser.contents.contains "users_id_positive"
  assert! getUser.contents.contains
    "@[expose] def ValidPred (value : RowData) : Prop :=\n  Pgx.Constraint.Valid checks value"
  assert! getUser.contents.contains "def SpecializedPred (value : RowData) : Prop"
  assert! getUser.contents.contains "theorem specializedPred_iff_validPred"
  assert! getUser.contents.contains "Pgx.Constraint.validatePredIff"
  assert! getUser.contents.contains "Pgx.Constraint.IntegerRange.HoldsValue"
  assert! getUser.contents.contains "def idUInt64 (value : Row) : UInt64"
  assert! getUser.contents.contains "Pgx.Constraint.uint64OfPositiveInt64"
  assert! !(getUser.contents.contains "Pgx.Constraint.compareNullable .gt")
  assert! getUser.contents.contains "match validate rowData with"
  assert! getUser.contents.contains "Pgx.Typed.Error.constraintViolation violation"
  let some listUsers := sources.findModule? "AppDb.Queries.ListUsers"
    | throw (IO.userError "missing generated ListUsers module")
  assert! listUsers.contents.contains "email : Option (AppDb.Types.AppEmailAddress)"
  assert! listUsers.contents.contains "| none => pure none"
  assert! listUsers.contents.contains "| some present => some <$> (do"
  assert! listUsers.contents.contains "resultFormats := #[1, 0, 0]"
  let some countUsers := sources.findModule? "AppDb.Queries.CountUsers"
    | throw (IO.userError "missing generated CountUsers module")
  assert! countUsers.contents.contains "resultFormats := #[1]"
  assert! !(countUsers.contents.contains "def countUInt64")

  -- Range recognition covers reversed operands, contradictory bounds and
  -- nullable SQL-unknown semantics.  Multiple recognized facts for `id`
  -- still emit one deterministic accessor declaration.
  assert! rangeSources.schema.contents.contains "users_id_positive_reversed"
  assert! rangeSources.schema.contents.contains "users_id_contradictory"
  assert! rangeSources.schema.contents.contains "users_score_range"
  assert! rangeSources.schema.contents.contains
    "Pgx.Constraint.IntegerRange.HoldsNullable"
  assert! rangeSources.schema.contents.contains "users_quantity_uint32"
  assert! rangeSources.schema.contents.contains
    "def quantityUInt32 (value : Row) : UInt32"
  assert! rangeSources.schema.contents.contains "Pgx.Constraint.uint32OfInt64"
  assert! (rangeSources.schema.contents.splitOn "def idUInt64 (value : Row)").length == 2
  let some mixedFormats := binaryFormatSources.findModule? "AppDb.Queries.MixedFormats"
    | throw (IO.userError "missing generated MixedFormats module")
  assert! mixedFormats.contents.contains
    "Option.map Pg.binaryInt32 params.count"
  assert! mixedFormats.contents.contains "Pg.binaryInt16 params.rank"
  assert! mixedFormats.contents.contains "resultFormats := #[1, 0]"
  assert! mixedFormats.contents.contains
    "decodeResolved External.citextCodec"
  assert! mixedFormats.contents.contains
    "Pg.PgEncode.encode (Option.map Pg.binaryInt32 params.count)"
  assert! mixedFormats.contents.contains
    "plannedBuiltinFormat (Option.map Pg.binaryInt32 params.count)"
  assert! mixedFormats.contents.contains
    "Pg.PgEncode.encode (Pg.binaryInt16 params.rank)"
  assert! mixedFormats.contents.contains
    "plannedBuiltinFormat (Pg.binaryInt16 params.rank)"
  assert! mixedFormats.contents.contains
    "values := #[Pg.PgEncode.encode (Option.map Pg.binaryInt32 params.count), Pg.PgEncode.encode (Pg.binaryInt16 params.rank)]"
  assert! mixedFormats.contents.contains
    "formats := #[Pgx.Typed.plannedBuiltinFormat (Option.map Pg.binaryInt32 params.count), Pgx.Typed.plannedBuiltinFormat (Pg.binaryInt16 params.rank)]"
  assert! !(mixedFormats.contents.contains "encodePlannedBuiltin")
  assert! mixedFormats.contents.contains
    "decodePlanned External.citextCodec resolve types[1]!"
  assert! mixedFormats.contents.contains
    "decodePlannedBuiltinSpan columns[0]!.typeOid columns[0]!.format values 0"
  assert! mixedFormats.contents.contains
    "decodePlannedSpan External.citextCodec resolve types[1]! columns[1]!.format values 1"

  -- Source contracts remain symbolic and unsupported types are hard errors.
  for source in sources.all do
    assert! !(source.contents.contains "90001")
  assert! isUnsupported (emitDatabase "AppDb" unsupported)
  assert! isError (emitDatabase "AppDb" (withImportModule ""))
  assert! isError (emitDatabase "AppDb" (withImportModule " Pg.Types.Codec"))
  assert! isError (emitDatabase "AppDb" forgedDomainAst)
  assert! isError (emitDatabase "AppDb" forgedDomainValidation)
  assert! isError (emitDatabase "AppDb" forgedRelationValidation)
  assert! isError (emitDatabase "AppDb" forgedQueryPlan)
  assert! isError (emitDatabase "AppDb" forgedRowPreservedRelation)
  assert! isError (emitDatabase "AppDb" forgedRowPreservedWidening)
  assert! isError (emitDatabase "AppDb" forgedRowPreservedWithoutOrigin)
  assert! isError (emitDatabase "AppDb" forgedLogicalWire)
  assert! isError (emitDatabase "AppDb" invalidCharacterTypmod)
  assert! isError (emitDatabase "AppDb" constrainedOverride)
  assert! isError (emitDatabase "AppDb" typmodOverride)
  return 0

end Pgx.Test.Emit

def main : IO UInt32 :=
  Pgx.Test.Emit.main
