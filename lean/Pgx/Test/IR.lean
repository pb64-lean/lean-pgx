import Pgx.TypeMapping

open Pgx

private def int4 : TypeRef :=
  { key := { schema := "pg_catalog", name := "int4", kind := .base } }

private def text : TypeRef :=
  { key := { schema := "pg_catalog", name := "text", kind := .base } }

private def status : TypeRef :=
  { key := { schema := "app", name := "status", kind := .enum } }

private def positiveId : TypeRef :=
  { key := { schema := "app", name := "positive_id", kind := .domain } }

private def statusArrayKey : TypeKey :=
  { schema := "app", name := "_status", kind := .array }

private def summaryKey : TypeKey :=
  { schema := "app", name := "user_summary", kind := .composite }

private def int4Scalar : Constraint.ScalarType := {
  declared := int4
  base := .int32
}

private def idComparison (op : Constraint.Comparison) (bound : Int) :
    Constraint.TruthExpr :=
  .compare op
    (.column "id" int4Scalar false)
    (.literal (.integer bound) int4Scalar)

private def queryConstraint (name source : String)
    (expression : Constraint.TruthExpr) : QueryConstraintIR := {
  relation := { schema := "app", name := "users" }
  name
  source
  expression
}

private def sample : DatabaseIR := {
  serverMajor := 18
  supportedServerMajors := #[18, 17]
  serverFeatures := #["identity-columns", "generated-columns"]
  session := { searchPath := #["app", "pg_catalog"] }
  schemas := #[{ name := "app" }]
  enums := #[{
    key := { schema := "app", name := "status", kind := .enum }
    labels := #["active", "disabled"]
  }]
  arrays := #[{ key := statusArrayKey, element := status }]
  domains := #[{
    key := { schema := "app", name := "positive_id", kind := .domain }
    base := int4
    notNull := true
    constraints := #["VALUE > 0", "VALUE < 2147483647"]
  }]
  composites := #[{
    key := summaryKey
    fields := #[
      { name := "id", ordinal := 1, ty := int4 },
      { name := "status", ordinal := 2, ty := status }
    ]
  }]
  relations := #[{
    key := { schema := "app", name := "users" }
    kind := .table
    columns := #[
      { name := "id", ordinal := 1, ty := positiveId, nullable := false },
      { name := "status", ordinal := 2, ty := status, nullable := false }
    ]
  }]
  views := #[{
    relation := { schema := "app", name := "active_users" }
    definition := " SELECT users.id FROM app.users WHERE users.status = 'active';"
    securityInvoker := true
  }]
  routines := #[{
    key := { schema := "app", name := "find_users", inputTypes := #[int4] }
    kind := .function
    args := #[
      { name := some "minimum_id", mode := .input, ty := int4 },
      { name := some "id", mode := .table, ty := int4 }
    ]
    returnsSet := true
    returnType := some { key := {
      schema := "pg_catalog", name := "record", kind := .pseudo } }
    resultColumns := #[{ name := "id", ordinal := 1, ty := int4 }]
    volatility := "s"
    parallel := "s"
  }]
  constraints := #[{
    relation := { schema := "app", name := "users" }
    name := "users_pkey"
    kind := .primaryKey
    columns := #["id"]
  }]
  indexes := #[]
  queries := #[{
    name := "GetUser"
    sql := "select id from app.users where id = $1"
    sqlHash := "abc"
    params := #[
      { position := 1, name := "id", ty := int4, nullable := false },
      { position := 2, name := "status", ty := status, nullable := false }
    ]
    columns := #[
      {
        name := "id"
        ty := int4
        logicalType := some positiveId
        nullable := false
        origin := some {
          relation := { schema := "app", name := "users" }
          name := "id"
        }
      },
      {
        name := "status"
        ty := status
        nullable := false
        origin := some {
          relation := { schema := "app", name := "users" }
          name := "status"
        }
      }
    ]
    rowPreservedRelations := #[{ schema := "app", name := "users" }]
    localConstraints := #[
      queryConstraint "users_id_positive" "CHECK (id > 0)"
        (idComparison .gt 0),
      queryConstraint "users_id_bounded" "CHECK (id < 2147483647)"
        (idComparison .lt 2147483647)
    ]
    cardinality := .zeroOrOne
  }]
}

private def shuffledFixture : DatabaseIR := {
  sample with
  schemas := sample.schemas.push { name := "audit" }
  enums := sample.enums.push {
    key := { schema := "audit", name := "action", kind := .enum }
    labels := #["insert", "update"]
  }
  domains := sample.domains.push {
    key := { schema := "audit", name := "actor", kind := .domain }
    base := text
    notNull := true
  }
  relations := sample.relations.push {
    key := { schema := "audit", name := "events" }
    kind := .table
    columns := #[{ name := "actor", ordinal := 1, ty := text, nullable := false }]
  }
  constraints := sample.constraints.push {
    relation := { schema := "audit", name := "events" }
    name := "events_actor_not_null"
    kind := .notNull
    columns := #["actor"]
  }
  indexes := #[
    {
      relation := { schema := "app", name := "users" }
      name := "users_id_key"
      unique := true
      primary := false
      valid := true
      columns := #["id"]
    },
    {
      relation := { schema := "audit", name := "events" }
      name := "events_actor_key"
      unique := true
      primary := false
      valid := true
      columns := #["actor"]
    }
  ]
  queries := sample.queries.push {
    name := "ListEvents"
    sql := "select actor from audit.events"
    sqlHash := "def"
    params := #[]
    columns := #[{ name := "actor", ty := text, nullable := false }]
    cardinality := .many
  }
  requiredExtensions := #[("uuid-ossp", "1.1"), ("citext", "1.6")]
  typeOverrides := #[
    {
      key := { schema := "ext", name := "first", kind := .base }
      leanType := "First"
      codec := "firstCodec"
      importModule := some "Ext.First"
    },
    {
      key := { schema := "ext", name := "second", kind := .base }
      leanType := "Second"
      codec := "secondCodec"
    }
  ]
}

private def shuffled (db : DatabaseIR) : DatabaseIR := {
  db with
  supportedServerMajors := db.supportedServerMajors.reverse
  serverFeatures := db.serverFeatures.reverse
  schemas := db.schemas.reverse
  enums := db.enums.reverse
  arrays := db.arrays.reverse
  domains := db.domains.reverse.map fun domain =>
    { domain with constraints := domain.constraints.reverse }
  composites := db.composites.reverse.map fun composite =>
    { composite with fields := composite.fields.reverse }
  ranges := db.ranges.reverse
  multiranges := db.multiranges.reverse
  relations := db.relations.reverse.map fun relation =>
    { relation with columns := relation.columns.reverse }
  views := db.views.reverse
  routines := db.routines.reverse
  constraints := db.constraints.reverse
  indexes := db.indexes.reverse
  queries := db.queries.reverse.map fun query =>
    { query with
      params := query.params.reverse
      rowPreservedRelations := query.rowPreservedRelations.reverse
      localConstraints := query.localConstraints.reverse }
  requiredExtensions := db.requiredExtensions.reverse
  typeOverrides := db.typeOverrides.reverse
  extensionCodecPackages := db.extensionCodecPackages.reverse.map fun package =>
    { package with types := package.types.reverse }
}

def main : IO UInt32 := do
  assert! sample.contractHash.length == 64
  assert! sample.compatibilityHash.length == 64
  assert! sample.contractHash == sample.contractHash
  assert! sample.normalize.supportedServerMajors == #[17, 18]
  assert! (builtinTypeMapping? int4.key).map (·.leanType) == some "Int32"
  assert! (sample.typeSupport? sample.enums[0]!.key).isSome
  assert! (sample.typeSupport? statusArrayKey).isSome
  let changedQueries := sample.queries.map fun (q : QueryIR) =>
    { q with columns := q.columns.map (fun (c : QueryColumnIR) =>
        { c with nullable := true }) }
  let changed : DatabaseIR := { sample with queries := changedQueries }
  assert! sample.contractHash != changed.contractHash
  let nullWidened : DatabaseIR := {
    sample with queries := sample.queries.map fun query => {
      query with columns := query.columns.map fun column =>
        { column with nullWidened := true }
    }
  }
  assert! sample.contractHash != nullWidened.contractHash
  let withoutLogicalType : DatabaseIR := {
    sample with queries := sample.queries.map fun query => {
      query with columns := query.columns.map fun column =>
        { column with logicalType := none }
    }
  }
  assert! sample.contractHash != withoutLogicalType.contractHash
  let withoutQueryConstraints : DatabaseIR := {
    sample with queries := sample.queries.map fun query =>
      { query with localConstraints := #[] }
  }
  assert! sample.contractHash != withoutQueryConstraints.contractHash
  let withoutRowPreservation : DatabaseIR := {
    sample with queries := sample.queries.map fun query =>
      { query with rowPreservedRelations := #[] }
  }
  assert! sample.contractHash != withoutRowPreservation.contractHash
  let reordered := shuffled shuffledFixture
  assert! shuffledFixture.normalize == reordered.normalize
  assert! shuffledFixture.contractHash == reordered.contractHash
  assert! shuffledFixture.compatibilityHash == reordered.compatibilityHash
  let previousMajor : DatabaseIR := { sample with serverMajor := 17 }
  assert! sample.contractHash != previousMajor.contractHash
  assert! sample.compatibilityHash == previousMajor.compatibilityHash
  let changedSupportedMajors : DatabaseIR := {
    sample with supportedServerMajors := #[18]
  }
  assert! sample.contractHash != changedSupportedMajors.contractHash
  assert! sample.compatibilityHash != changedSupportedMajors.compatibilityHash
  let withEmptySchema : DatabaseIR := {
    sample with schemas := sample.schemas.push { name := "empty" }
  }
  assert! sample.contractHash != withEmptySchema.contractHash
  let changedSearchPath : DatabaseIR := {
    sample with session := { sample.session with searchPath := sample.session.searchPath.reverse }
  }
  assert! sample.contractHash != changedSearchPath.contractHash
  let changedEnumOrder : DatabaseIR := {
    sample with enums := sample.enums.map fun value => { value with labels := value.labels.reverse }
  }
  assert! sample.contractHash != changedEnumOrder.contractHash
  let changedColumnOrder : DatabaseIR := {
    sample with queries := sample.queries.map fun query =>
      { query with columns := query.columns.reverse }
  }
  assert! sample.contractHash != changedColumnOrder.contractHash
  let changedOverrideImport : DatabaseIR := {
    shuffledFixture with
    typeOverrides := shuffledFixture.typeOverrides.map fun value =>
      if value.key.name == "first" then
        { value with importModule := some "Ext.First.V2" }
      else value
  }
  assert! shuffledFixture.contractHash != changedOverrideImport.contractHash
  assert! shuffledFixture.compatibilityHash != changedOverrideImport.compatibilityHash
  let changedComposite : DatabaseIR := {
    sample with composites := sample.composites.map fun value =>
      { value with fields := value.fields.map fun field =>
          if field.name == "id" then { field with ty := text } else field }
  }
  assert! sample.contractHash != changedComposite.contractHash
  let changedView : DatabaseIR := {
    sample with views := sample.views.map fun value =>
      { value with securityBarrier := !value.securityBarrier }
  }
  assert! sample.contractHash != changedView.contractHash
  let changedRoutine : DatabaseIR := {
    sample with routines := sample.routines.map fun value =>
      { value with returnsSet := !value.returnsSet }
  }
  assert! sample.contractHash != changedRoutine.contractHash
  let oidText := reprStr sample
  assert! !(oidText.contains "tableOid")
  return 0
