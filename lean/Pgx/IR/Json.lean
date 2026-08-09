import Pgx.IR
import Lean.Data.Json

/-!
# Canonical JSON for the PostgreSQL IR

The JSON representation in this module is deliberately explicit.  In
particular it does not depend on the compiler-generated encoding used by
`deriving ToJson`, so snapshots remain stable when declaration details change.

`DatabaseIR` values are normalized before they are encoded.  Arrays whose
order is semantic are preserved by `DatabaseIR.normalize`; set-like arrays are
sorted there before this module renders them.
-/

namespace Pgx

open Lean

private def requiredField [FromJson α]
    (json : Json) (field : String) : Except String α := do
  let value ← match json.getObjVal? field with
    | .ok value => pure value
    | .error error => throw s!"field '{field}': {error}"
  match fromJson? value with
  | .ok result => pure result
  | .error error => throw s!"field '{field}': {error}"

private def optionalField [FromJson α]
    (json : Json) (field : String) (default : α) : Except String α := do
  let object ← json.getObj?
  match object.get? field with
  | none => pure default
  | some value =>
      match fromJson? value with
      | .ok result => pure result
      | .error error => throw s!"field '{field}': {error}"

private def tagFromJson
    (typeName : String) (decode : String → Option α) (json : Json) :
    Except String α := do
  let tag ← json.getStr?
  match decode tag with
  | some value => pure value
  | none => throw s!"unsupported {typeName} '{tag}'"

private def int32ToJson (value : Int32) : Json :=
  Json.num value.toInt

private def int32FromJson (json : Json) : Except String Int32 := do
  let value ← json.getInt?
  if Int32.minValue.toInt ≤ value ∧ value ≤ Int32.maxValue.toInt then
    pure (Int32.ofInt value)
  else
    throw s!"integer '{value}' is outside the Int32 range"

private def optionInt32ToJson : Option Int32 → Json
  | none => Json.null
  | some value => int32ToJson value

private def optionInt32FromJson : Json → Except String (Option Int32)
  | .null => pure none
  | json => some <$> int32FromJson json

instance : ToJson TypeKind where
  toJson value := Json.str value.tag

instance : FromJson TypeKind where
  fromJson? := tagFromJson "type kind" fun
    | "base" => some .base
    | "enum" => some .enum
    | "domain" => some .domain
    | "array" => some .array
    | "range" => some .range
    | "multirange" => some .multirange
    | "composite" => some .composite
    | "pseudo" => some .pseudo
    | _ => none

instance : ToJson TypeKey where
  toJson value := Json.mkObj [
    ("schema", toJson value.schema),
    ("name", toJson value.name),
    ("kind", toJson value.kind)
  ]

instance : FromJson TypeKey where
  fromJson? json := do
    pure {
      schema := ← requiredField json "schema"
      name := ← requiredField json "name"
      kind := ← requiredField json "kind"
    }

instance : ToJson TypeRef where
  toJson value := Json.mkObj [
    ("key", toJson value.key),
    ("typmod", optionInt32ToJson value.typmod)
  ]

instance : FromJson TypeRef where
  fromJson? json := do
    let typmod ← match (json.getObj? : Except String (Std.TreeMap.Raw String Json compare)) with
      | .error error => throw error
      | .ok object =>
          match object.get? "typmod" with
          | none => pure none
          | some value => optionInt32FromJson value
    pure {
      key := ← requiredField json "key"
      typmod
    }

instance : ToJson RelationKey where
  toJson value := Json.mkObj [
    ("schema", toJson value.schema),
    ("name", toJson value.name)
  ]

instance : FromJson RelationKey where
  fromJson? json := do
    pure {
      schema := ← requiredField json "schema"
      name := ← requiredField json "name"
    }

instance : ToJson ColumnKey where
  toJson value := Json.mkObj [
    ("relation", toJson value.relation),
    ("name", toJson value.name)
  ]

instance : FromJson ColumnKey where
  fromJson? json := do
    pure {
      relation := ← requiredField json "relation"
      name := ← requiredField json "name"
    }

instance : ToJson CollationKey where
  toJson value := Json.mkObj [
    ("schema", toJson value.schema),
    ("name", toJson value.name)
  ]

instance : FromJson CollationKey where
  fromJson? json := do
    pure {
      schema := ← requiredField json "schema"
      name := ← requiredField json "name"
    }

instance : ToJson SchemaIR where
  toJson value := Json.mkObj [("name", toJson value.name)]

instance : FromJson SchemaIR where
  fromJson? json := do
    pure { name := ← requiredField json "name" }

instance : ToJson EnumIR where
  toJson value := Json.mkObj [
    ("key", toJson value.key),
    ("labels", toJson value.labels)
  ]

instance : FromJson EnumIR where
  fromJson? json := do
    pure {
      key := ← requiredField json "key"
      labels := ← requiredField json "labels"
    }

instance : ToJson DomainIR where
  toJson value := Json.mkObj [
    ("key", toJson value.key),
    ("base", toJson value.base),
    ("notNull", toJson value.notNull),
    ("defaultExpr", toJson value.defaultExpr),
    ("constraints", toJson value.constraints)
  ]

instance : FromJson DomainIR where
  fromJson? json := do
    pure {
      key := ← requiredField json "key"
      base := ← requiredField json "base"
      notNull := ← requiredField json "notNull"
      defaultExpr := ← optionalField json "defaultExpr" none
      constraints := ← optionalField json "constraints" #[]
    }

instance : ToJson RelationKind where
  toJson value := Json.str value.tag

instance : FromJson RelationKind where
  fromJson? := tagFromJson "relation kind" fun
    | "table" => some .table
    | "partitioned-table" => some .partitionedTable
    | "view" => some .view
    | "materialized-view" => some .materializedView
    | "foreign-table" => some .foreignTable
    | _ => none

instance : ToJson RelationColumnIR where
  toJson value := Json.mkObj [
    ("name", toJson value.name),
    ("ordinal", toJson value.ordinal),
    ("type", toJson value.ty),
    ("nullable", toJson value.nullable),
    ("identity", toJson value.identity),
    ("generated", toJson value.generated),
    ("defaultExpr", toJson value.defaultExpr),
    ("collation", toJson value.collation)
  ]

instance : FromJson RelationColumnIR where
  fromJson? json := do
    pure {
      name := ← requiredField json "name"
      ordinal := ← requiredField json "ordinal"
      ty := ← requiredField json "type"
      nullable := ← requiredField json "nullable"
      identity := ← optionalField json "identity" false
      generated := ← optionalField json "generated" false
      defaultExpr := ← optionalField json "defaultExpr" none
      collation := ← optionalField json "collation" none
    }

instance : ToJson RelationIR where
  toJson value := Json.mkObj [
    ("key", toJson value.key),
    ("kind", toJson value.kind),
    ("columns", toJson value.columns)
  ]

instance : FromJson RelationIR where
  fromJson? json := do
    pure {
      key := ← requiredField json "key"
      kind := ← requiredField json "kind"
      columns := ← requiredField json "columns"
    }

instance : ToJson ConstraintKind where
  toJson value := Json.str value.tag

instance : FromJson ConstraintKind where
  fromJson? := tagFromJson "constraint kind" fun
    | "check" => some .check
    | "not-null" => some .notNull
    | "primary-key" => some .primaryKey
    | "unique" => some .unique
    | "foreign-key" => some .foreignKey
    | "exclusion" => some .exclusion
    | _ => none

instance : ToJson ConstraintIR where
  toJson value := Json.mkObj [
    ("relation", toJson value.relation),
    ("name", toJson value.name),
    ("kind", toJson value.kind),
    ("columns", toJson value.columns),
    ("referencedRelation", toJson value.referencedRelation),
    ("referencedColumns", toJson value.referencedColumns),
    ("expression", toJson value.expression),
    ("validated", toJson value.validated)
  ]

instance : FromJson ConstraintIR where
  fromJson? json := do
    pure {
      relation := ← requiredField json "relation"
      name := ← requiredField json "name"
      kind := ← requiredField json "kind"
      columns := ← optionalField json "columns" #[]
      referencedRelation := ← optionalField json "referencedRelation" none
      referencedColumns := ← optionalField json "referencedColumns" #[]
      expression := ← optionalField json "expression" none
      validated := ← optionalField json "validated" true
    }

instance : ToJson IndexIR where
  toJson value := Json.mkObj [
    ("relation", toJson value.relation),
    ("name", toJson value.name),
    ("unique", toJson value.unique),
    ("primary", toJson value.primary),
    ("valid", toJson value.valid),
    ("columns", toJson value.columns),
    ("predicate", toJson value.predicate),
    ("expression", toJson value.expression)
  ]

instance : FromJson IndexIR where
  fromJson? json := do
    pure {
      relation := ← requiredField json "relation"
      name := ← requiredField json "name"
      unique := ← requiredField json "unique"
      primary := ← requiredField json "primary"
      valid := ← requiredField json "valid"
      columns := ← optionalField json "columns" #[]
      predicate := ← optionalField json "predicate" none
      expression := ← optionalField json "expression" none
    }

instance : ToJson Cardinality where
  toJson value := Json.str value.tag

instance : FromJson Cardinality where
  fromJson? := tagFromJson "cardinality" fun
    | "execute" => some .execute
    | "exactlyOne" => some .exactlyOne
    | "zeroOrOne" => some .zeroOrOne
    | "many" => some .many
    | _ => none

instance : ToJson ParamIR where
  toJson value := Json.mkObj [
    ("position", toJson value.position),
    ("name", toJson value.name),
    ("type", toJson value.ty),
    ("nullable", toJson value.nullable)
  ]

instance : FromJson ParamIR where
  fromJson? json := do
    pure {
      position := ← requiredField json "position"
      name := ← requiredField json "name"
      ty := ← requiredField json "type"
      nullable := ← requiredField json "nullable"
    }

instance : ToJson QueryColumnIR where
  toJson value := Json.mkObj [
    ("name", toJson value.name),
    ("type", toJson value.ty),
    ("nullable", toJson value.nullable),
    ("origin", toJson value.origin),
    ("collation", toJson value.collation)
  ]

instance : FromJson QueryColumnIR where
  fromJson? json := do
    pure {
      name := ← requiredField json "name"
      ty := ← requiredField json "type"
      nullable := ← requiredField json "nullable"
      origin := ← optionalField json "origin" none
      collation := ← optionalField json "collation" none
    }

instance : ToJson QueryIR where
  toJson value := Json.mkObj [
    ("name", toJson value.name),
    ("sql", toJson value.sql),
    ("sqlHash", toJson value.sqlHash),
    ("params", toJson value.params),
    ("columns", toJson value.columns),
    ("cardinality", toJson value.cardinality)
  ]

instance : FromJson QueryIR where
  fromJson? json := do
    pure {
      name := ← requiredField json "name"
      sql := ← requiredField json "sql"
      sqlHash := ← requiredField json "sqlHash"
      params := ← requiredField json "params"
      columns := ← requiredField json "columns"
      cardinality := ← requiredField json "cardinality"
    }

instance : ToJson SessionContract where
  toJson value := Json.mkObj [
    ("searchPath", toJson value.searchPath),
    ("timezone", toJson value.timezone),
    ("encoding", toJson value.encoding),
    ("standardConformingStrings", toJson value.standardConformingStrings)
  ]

instance : FromJson SessionContract where
  fromJson? json := do
    pure {
      searchPath := ← requiredField json "searchPath"
      timezone := ← optionalField json "timezone" "UTC"
      encoding := ← optionalField json "encoding" "UTF8"
      standardConformingStrings := ← optionalField json "standardConformingStrings" true
    }

instance : ToJson TypeOverrideIR where
  toJson value :=
    let fields := [
      ("key", toJson value.key),
      ("leanType", toJson value.leanType),
      ("codec", toJson value.codec)
    ]
    let fields := match value.importModule with
      | none => fields
      | some moduleName => fields ++ [("importModule", toJson moduleName)]
    Json.mkObj fields

instance : FromJson TypeOverrideIR where
  fromJson? json := do
    pure {
      key := ← requiredField json "key"
      leanType := ← requiredField json "leanType"
      codec := ← requiredField json "codec"
      importModule := ← optionalField json "importModule" none
    }

private def extensionToJson (value : String × String) : Json :=
  Json.mkObj [
    ("name", toJson value.1),
    ("version", toJson value.2)
  ]

private def extensionFromJson (json : Json) : Except String (String × String) := do
  pure (← requiredField json "name", ← requiredField json "version")

private def extensionsToJson (values : Array (String × String)) : Json :=
  Json.arr (values.map extensionToJson)

private def extensionsFromJson (json : Json) : Except String (Array (String × String)) := do
  let values ← json.getArr?
  values.mapM extensionFromJson

private def databaseToJson (value : DatabaseIR) : Json :=
  Json.mkObj [
    ("formatVersion", toJson value.formatVersion),
    ("serverMajor", toJson value.serverMajor),
    ("serverFeatures", toJson value.serverFeatures),
    ("session", toJson value.session),
    ("schemas", toJson value.schemas),
    ("enums", toJson value.enums),
    ("domains", toJson value.domains),
    ("relations", toJson value.relations),
    ("constraints", toJson value.constraints),
    ("indexes", toJson value.indexes),
    ("queries", toJson value.queries),
    ("requiredExtensions", extensionsToJson value.requiredExtensions),
    ("typeOverrides", toJson value.typeOverrides)
  ]

instance : ToJson DatabaseIR where
  toJson value := databaseToJson value.normalize

instance : FromJson DatabaseIR where
  fromJson? json := do
    let requiredExtensions ← do
      let object ← json.getObj?
      match object.get? "requiredExtensions" with
      | none => pure #[]
      | some value =>
          match extensionsFromJson value with
          | .ok result => pure result
          | .error error => throw s!"field 'requiredExtensions': {error}"
    pure {
      formatVersion := ← optionalField json "formatVersion" 1
      serverMajor := ← requiredField json "serverMajor"
      serverFeatures := ← optionalField json "serverFeatures" #[]
      session := ← requiredField json "session"
      schemas := ← requiredField json "schemas"
      enums := ← requiredField json "enums"
      domains := ← requiredField json "domains"
      relations := ← requiredField json "relations"
      constraints := ← requiredField json "constraints"
      indexes := ← requiredField json "indexes"
      queries := ← requiredField json "queries"
      requiredExtensions
      typeOverrides := ← optionalField json "typeOverrides" #[]
    }

namespace DatabaseIR

/-- The normalized JSON value written to a `.pgir.json` snapshot. -/
def snapshotJson (database : DatabaseIR) : Json :=
  toJson database

/-- Render a deterministic, human-readable `.pgir.json` document. -/
def renderSnapshot (database : DatabaseIR) : String :=
  database.snapshotJson.pretty ++ "\n"

/-- Render a deterministic compact snapshot, useful for action inputs/hashes. -/
def renderSnapshotCompact (database : DatabaseIR) : String :=
  database.snapshotJson.compress

/-- Decode a snapshot JSON value and reject unsupported format versions. -/
def parseSnapshotJson (json : Json) : Except String DatabaseIR := do
  let database : DatabaseIR ← fromJson? json
  if database.formatVersion == 1 then
    pure database.normalize
  else
    throw s!"unsupported Pgx IR format version {database.formatVersion}"

/-- Parse and decode a `.pgir.json` document. -/
def parseSnapshot (document : String) : Except String DatabaseIR := do
  let json ← Json.parse document
  parseSnapshotJson json

end DatabaseIR

end Pgx
