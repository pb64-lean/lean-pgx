import Pgx.IR.Json

open Pgx
open Lean

private def int4 : TypeRef := {
  key := { schema := "pg_catalog", name := "int4", kind := .base }
}

private def database (serverMajor : Nat) : DatabaseIR := {
  serverMajor
  supportedServerMajors := #[17, 18]
  session := { searchPath := #["app", "pg_catalog"] }
  schemas := #[{ name := "app" }]
  enums := #[]
  domains := #[]
  relations := #[{
    key := { schema := "app", name := "users" }
    kind := .table
    columns := #[{
      name := "id"
      ordinal := 1
      ty := int4
      nullable := false
    }]
  }]
  constraints := #[]
  indexes := #[]
  queries := #[{
    name := "GetUser"
    sql := "select id from app.users where id = $1"
    sqlHash := "query-hash"
    params := #[{
      position := 1
      name := "id"
      ty := int4
      nullable := false
    }]
    columns := #[{
      name := "id"
      ty := int4
      nullable := false
      origin := some {
        relation := { schema := "app", name := "users" }
        name := "id"
      }
    }]
    cardinality := .zeroOrOne
  }]
}

private def int4Operator (name : String) : OperatorKey := {
  schema := "pg_catalog"
  name
  leftType := int4.key
  rightType := int4.key
}

private def indexElement (ordinal : Nat) (column : String) : IndexKeyElementIR := {
  ordinal
  column := some column
  collation := some { schema := "pg_catalog", name := "default" }
  opclass := some { schema := "pg_catalog", name := "int4_ops" }
  equalityOperator := some (int4Operator "=")
  order := .descending
  nullsOrder := .first
}

private def relationalDatabase : DatabaseIR := {
  database 18 with
  constraints := #[
    {
      relation := { schema := "app", name := "orders" }
      name := "orders_user_fkey"
      kind := .foreignKey
      columns := #["tenant_id", "user_id"]
      referencedRelation := some { schema := "app", name := "users" }
      referencedColumns := #["tenant_id", "id"]
      expression := some "FOREIGN KEY (tenant_id, user_id)"
      enforced := false
      validated := false
      deferrable := true
      initiallyDeferred := true
      parent := some {
        relation := { schema := "app", name := "orders_parent" }
        name := "orders_parent_user_fkey"
      }
      isLocal := false
      inheritanceCount := 2
      noInherit := true
      period := true
      supportingIndex := some { schema := "app", name := "users_tenant_id_key" }
      foreignKeyMatch := .full
      foreignKeyOnUpdate := .cascade
      foreignKeyOnDelete := .setDefault
      foreignKeyDeleteSetColumns := #["user_id", "tenant_id"]
      referencedToReferencingOperators :=
        #[int4Operator "=", int4Operator "~="]
      referencedEqualityOperators :=
        #[int4Operator "=", int4Operator "~="]
      referencingEqualityOperators :=
        #[int4Operator "~=", int4Operator "="]
    },
    {
      relation := { schema := "app", name := "bookings" }
      name := "bookings_no_overlap"
      kind := .exclusion
      supportingIndex := some { schema := "app", name := "bookings_no_overlap" }
      exclusionElements := #[
        { key := indexElement 2 "during", operator := int4Operator "&&" },
        { key := indexElement 1 "room_id", operator := int4Operator "=" }
      ]
    },
    {
      relation := { schema := "app", name := "users" }
      name := "users_tenant_id_key"
      kind := .unique
      columns := #["tenant_id", "id"]
      supportingIndex := some { schema := "app", name := "users_tenant_id_key" }
      uniqueNullPolicy := .notDistinct
    }
  ]
  indexes := #[
    {
      relation := { schema := "app", name := "users" }
      name := "users_tenant_id_key"
      unique := true
      primary := false
      valid := true
      immediate := false
      ready := false
      live := false
      uniqueNullPolicy := .notDistinct
      accessMethod := some "btree"
      columns := #["tenant_id", "id"]
      keyElements := #[indexElement 2 "id", indexElement 1 "tenant_id"]
      includedColumns := #["display_name", "status"]
      predicate := some "tenant_id IS NOT NULL"
      expression := some "lower(id::text)"
    },
    {
      relation := { schema := "app", name := "bookings" }
      name := "bookings_no_overlap"
      unique := false
      primary := false
      exclusion := true
      valid := true
      accessMethod := some "gist"
      keyElements := #[indexElement 1 "room_id", indexElement 2 "during"]
    }
  ]
}

private def legacyConstraintJson : Json := Json.mkObj [
  ("relation", Json.mkObj [
    ("schema", Json.str "app"),
    ("name", Json.str "orders")
  ]),
  ("name", Json.str "orders_user_fkey"),
  ("kind", Json.str "foreign-key")
]

private def legacyIndexJson : Json := Json.mkObj [
  ("relation", Json.mkObj [
    ("schema", Json.str "app"),
    ("name", Json.str "users")
  ]),
  ("name", Json.str "users_pkey"),
  ("unique", Json.bool true),
  ("primary", Json.bool true),
  ("valid", Json.bool true)
]

private def legacyIndexElementJson : Json := Json.mkObj [
  ("ordinal", Json.num 1),
  ("column", Json.str "id")
]

def main : IO UInt32 := do
  let pg17 := database 17
  let pg18 := database 18
  -- The ordinary contract fingerprints the canonical server major.
  assert! pg17.contractHash != pg18.contractHash
  -- Compatibility deliberately ignores only that major difference.
  assert! pg17.compatibilityHash == pg18.compatibilityHash

  let driftedQueries := pg18.queries.map fun query => {
    query with columns := query.columns.map fun column => {
      column with nullable := true
    }
  }
  let drifted : DatabaseIR := { pg18 with queries := driftedQueries }
  assert! pg17.compatibilityHash != drifted.compatibilityHash

  let roundTripped ←
    match DatabaseIR.parseSnapshot relationalDatabase.renderSnapshot with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! roundTripped == relationalDatabase.normalize

  let legacyConstraint ←
    match (fromJson? legacyConstraintJson : Except String ConstraintIR) with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! legacyConstraint.enforced
  assert! legacyConstraint.validated
  assert! !legacyConstraint.deferrable
  assert! !legacyConstraint.initiallyDeferred
  assert! legacyConstraint.parent.isNone
  assert! legacyConstraint.isLocal
  assert! legacyConstraint.inheritanceCount == 0
  assert! !legacyConstraint.noInherit
  assert! !legacyConstraint.period
  assert! legacyConstraint.supportingIndex.isNone
  assert! legacyConstraint.uniqueNullPolicy == .distinct
  assert! legacyConstraint.foreignKeyMatch == .simple
  assert! legacyConstraint.foreignKeyOnUpdate == .noAction
  assert! legacyConstraint.foreignKeyOnDelete == .noAction
  assert! legacyConstraint.foreignKeyDeleteSetColumns.isEmpty
  assert! legacyConstraint.referencedToReferencingOperators.isEmpty
  assert! legacyConstraint.referencedEqualityOperators.isEmpty
  assert! legacyConstraint.referencingEqualityOperators.isEmpty
  assert! legacyConstraint.exclusionElements.isEmpty

  let legacyIndex ←
    match (fromJson? legacyIndexJson : Except String IndexIR) with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! !legacyIndex.exclusion
  assert! legacyIndex.immediate
  assert! legacyIndex.ready
  assert! legacyIndex.live
  assert! legacyIndex.uniqueNullPolicy == .distinct
  assert! legacyIndex.accessMethod.isNone
  assert! legacyIndex.keyElements.isEmpty
  assert! legacyIndex.includedColumns.isEmpty

  let legacyIndexElement ←
    match (fromJson? legacyIndexElementJson : Except String IndexKeyElementIR) with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! legacyIndexElement.equalityOperator.isNone
  assert! legacyIndexElement.order == .ascending
  assert! legacyIndexElement.nullsOrder == .last

  let version3Document :=
    (database 18).renderSnapshot.replace "\"formatVersion\": 4" "\"formatVersion\": 3"
  let version3 ←
    match DatabaseIR.parseSnapshot version3Document with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  assert! version3.formatVersion == 3
  return 0
