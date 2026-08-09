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

instance : ToJson Constraint.ScalarKind where
  toJson value := match value with
    | .boolean => Json.mkObj [("tag", "boolean")]
    | .int16 => Json.mkObj [("tag", "int16")]
    | .int32 => Json.mkObj [("tag", "int32")]
    | .int64 => Json.mkObj [("tag", "int64")]
    | .numeric => Json.mkObj [("tag", "numeric")]
    | .text => Json.mkObj [("tag", "text")]
    | .enumeration key => Json.mkObj [
        ("tag", "enumeration"),
        ("key", toJson key)
      ]

instance : FromJson Constraint.ScalarKind where
  fromJson? json := do
    let tag : String ← requiredField json "tag"
    match tag with
    | "boolean" => pure .boolean
    | "int16" => pure .int16
    | "int32" => pure .int32
    | "int64" => pure .int64
    | "numeric" => pure .numeric
    | "text" => pure .text
    | "enumeration" => pure (.enumeration (← requiredField json "key"))
    | _ => throw s!"unsupported constraint scalar kind '{tag}'"

instance : ToJson Constraint.ScalarType where
  toJson value := Json.mkObj [
    ("declared", toJson value.declared),
    ("base", toJson value.base),
    ("domains", toJson value.domains)
  ]

instance : FromJson Constraint.ScalarType where
  fromJson? json := do
    pure {
      declared := ← requiredField json "declared"
      base := ← requiredField json "base"
      domains := ← optionalField json "domains" #[]
    }

instance : ToJson Constraint.Literal where
  toJson value := match value with
    | .null => Json.mkObj [("tag", "null")]
    | .boolean value => Json.mkObj [
        ("tag", "boolean"),
        ("value", toJson value)
      ]
    | .integer value => Json.mkObj [
        ("tag", "integer"),
        ("value", toJson value)
      ]
    | .numeric value => Json.mkObj [
        ("tag", "numeric"),
        ("value", toJson value)
      ]
    | .text value => Json.mkObj [
        ("tag", "text"),
        ("value", toJson value)
      ]
    | .enumeration key label => Json.mkObj [
        ("tag", "enumeration"),
        ("key", toJson key),
        ("label", toJson label)
      ]

instance : FromJson Constraint.Literal where
  fromJson? json := do
    let tag : String ← requiredField json "tag"
    match tag with
    | "null" => pure .null
    | "boolean" => pure (.boolean (← requiredField json "value"))
    | "integer" => pure (.integer (← requiredField json "value"))
    | "numeric" => pure (.numeric (← requiredField json "value"))
    | "text" => pure (.text (← requiredField json "value"))
    | "enumeration" => pure (.enumeration
        (← requiredField json "key") (← requiredField json "label"))
    | _ => throw s!"unsupported constraint literal kind '{tag}'"

instance : ToJson Constraint.CastPreservation where
  toJson value := Json.str <| match value with
    | .identity => "identity"
    | .domain => "domain"
    | .integerWiden => "integer-widen"
    | .exactNumeric => "exact-numeric"
    | .textRepresentation => "text-representation"
    | .enumLiteral => "enum-literal"

instance : FromJson Constraint.CastPreservation where
  fromJson? := tagFromJson "constraint cast preservation" fun
    | "identity" => some .identity
    | "domain" => some .domain
    | "integer-widen" => some .integerWiden
    | "exact-numeric" => some .exactNumeric
    | "text-representation" => some .textRepresentation
    | "enum-literal" => some .enumLiteral
    | _ => none

private partial def constraintValueExprToJson : Constraint.ValueExpr → Json
  | .column name ty nullable => Json.mkObj [
      ("tag", "column"), ("name", toJson name), ("type", toJson ty),
      ("nullable", toJson nullable)
    ]
  | .domainValue ty nullable => Json.mkObj [
      ("tag", "domain-value"), ("type", toJson ty),
      ("nullable", toJson nullable)
    ]
  | .literal value ty => Json.mkObj [
      ("tag", "literal"), ("literal", toJson value), ("type", toJson ty)
    ]
  | .cast preservation value target => Json.mkObj [
      ("tag", "cast"), ("preservation", toJson preservation),
      ("value", constraintValueExprToJson value), ("target", toJson target)
    ]
  | .neg value result => Json.mkObj [
      ("tag", "neg"), ("value", constraintValueExprToJson value),
      ("result", toJson result)
    ]
  | .add left right result => Json.mkObj [
      ("tag", "add"), ("left", constraintValueExprToJson left),
      ("right", constraintValueExprToJson right), ("result", toJson result)
    ]
  | .sub left right result => Json.mkObj [
      ("tag", "sub"), ("left", constraintValueExprToJson left),
      ("right", constraintValueExprToJson right), ("result", toJson result)
    ]
  | .charLength value result => Json.mkObj [
      ("tag", "char-length"), ("value", constraintValueExprToJson value),
      ("result", toJson result)
    ]
  | .btrim value result => Json.mkObj [
      ("tag", "btrim"), ("value", constraintValueExprToJson value),
      ("result", toJson result)
    ]
  | .position substring string result => Json.mkObj [
      ("tag", "position"), ("substring", constraintValueExprToJson substring),
      ("string", constraintValueExprToJson string), ("result", toJson result)
    ]

private partial def constraintValueExprFromJson (json : Json) :
    Except String Constraint.ValueExpr := do
  let tag : String ← requiredField json "tag"
  match tag with
  | "column" => pure (.column (← requiredField json "name")
      (← requiredField json "type") (← requiredField json "nullable"))
  | "domain-value" => pure (.domainValue (← requiredField json "type")
      (← requiredField json "nullable"))
  | "literal" => pure (.literal (← requiredField json "literal")
      (← requiredField json "type"))
  | "cast" => pure (.cast (← requiredField json "preservation")
      (← constraintValueExprFromJson (← requiredField json "value"))
      (← requiredField json "target"))
  | "neg" => pure (.neg
      (← constraintValueExprFromJson (← requiredField json "value"))
      (← requiredField json "result"))
  | "add" => pure (.add
      (← constraintValueExprFromJson (← requiredField json "left"))
      (← constraintValueExprFromJson (← requiredField json "right"))
      (← requiredField json "result"))
  | "sub" => pure (.sub
      (← constraintValueExprFromJson (← requiredField json "left"))
      (← constraintValueExprFromJson (← requiredField json "right"))
      (← requiredField json "result"))
  | "char-length" => pure (.charLength
      (← constraintValueExprFromJson (← requiredField json "value"))
      (← requiredField json "result"))
  | "btrim" => pure (.btrim
      (← constraintValueExprFromJson (← requiredField json "value"))
      (← requiredField json "result"))
  | "position" => pure (.position
      (← constraintValueExprFromJson (← requiredField json "substring"))
      (← constraintValueExprFromJson (← requiredField json "string"))
      (← requiredField json "result"))
  | _ => throw s!"unsupported constraint value expression '{tag}'"

instance : ToJson Constraint.ValueExpr where
  toJson := constraintValueExprToJson

instance : FromJson Constraint.ValueExpr where
  fromJson? := constraintValueExprFromJson

instance : ToJson Constraint.Comparison where
  toJson value := Json.str <| match value with
    | .eq => "eq"
    | .ne => "ne"
    | .lt => "lt"
    | .le => "le"
    | .gt => "gt"
    | .ge => "ge"

instance : FromJson Constraint.Comparison where
  fromJson? := tagFromJson "constraint comparison" fun
    | "eq" => some .eq
    | "ne" => some .ne
    | "lt" => some .lt
    | "le" => some .le
    | "gt" => some .gt
    | "ge" => some .ge
    | _ => none

private partial def constraintTruthExprToJson : Constraint.TruthExpr → Json
  | .constant value => Json.mkObj [
      ("tag", "constant"), ("value", toJson value)
    ]
  | .fromBoolean value => Json.mkObj [
      ("tag", "from-boolean"), ("value", toJson value)
    ]
  | .compare op left right => Json.mkObj [
      ("tag", "compare"), ("operator", toJson op),
      ("left", toJson left), ("right", toJson right)
    ]
  | .isNull value => Json.mkObj [
      ("tag", "is-null"), ("value", toJson value)
    ]
  | .isNotNull value => Json.mkObj [
      ("tag", "is-not-null"), ("value", toJson value)
    ]
  | .and left right => Json.mkObj [
      ("tag", "and"), ("left", constraintTruthExprToJson left),
      ("right", constraintTruthExprToJson right)
    ]
  | .or left right => Json.mkObj [
      ("tag", "or"), ("left", constraintTruthExprToJson left),
      ("right", constraintTruthExprToJson right)
    ]
  | .not value => Json.mkObj [
      ("tag", "not"), ("value", constraintTruthExprToJson value)
    ]

private partial def constraintTruthExprFromJson (json : Json) :
    Except String Constraint.TruthExpr := do
  let tag : String ← requiredField json "tag"
  match tag with
  | "constant" => pure (.constant (← requiredField json "value"))
  | "from-boolean" => pure (.fromBoolean (← requiredField json "value"))
  | "compare" => pure (.compare (← requiredField json "operator")
      (← requiredField json "left") (← requiredField json "right"))
  | "is-null" => pure (.isNull (← requiredField json "value"))
  | "is-not-null" => pure (.isNotNull (← requiredField json "value"))
  | "and" => pure (.and
      (← constraintTruthExprFromJson (← requiredField json "left"))
      (← constraintTruthExprFromJson (← requiredField json "right")))
  | "or" => pure (.or
      (← constraintTruthExprFromJson (← requiredField json "left"))
      (← constraintTruthExprFromJson (← requiredField json "right")))
  | "not" => pure (.not (← constraintTruthExprFromJson
      (← requiredField json "value")))
  | _ => throw s!"unsupported constraint truth expression '{tag}'"

instance : ToJson Constraint.TruthExpr where
  toJson := constraintTruthExprToJson

instance : FromJson Constraint.TruthExpr where
  fromJson? := constraintTruthExprFromJson

instance : ToJson DomainConstraintIR where
  toJson value := Json.mkObj [
    ("name", toJson value.name),
    ("source", toJson value.source),
    ("expression", toJson value.expression),
    ("validated", toJson value.validated)
  ]

instance : FromJson DomainConstraintIR where
  fromJson? json := do
    pure {
      name := ← requiredField json "name"
      source := ← requiredField json "source"
      expression := ← requiredField json "expression"
      validated := ← optionalField json "validated" true
    }

instance : ToJson DomainIR where
  toJson value := Json.mkObj [
    ("key", toJson value.key),
    ("base", toJson value.base),
    ("notNull", toJson value.notNull),
    ("defaultExpr", toJson value.defaultExpr),
    ("constraints", toJson value.constraints),
    ("localConstraints", toJson value.localConstraints)
  ]

instance : FromJson DomainIR where
  fromJson? json := do
    pure {
      key := ← requiredField json "key"
      base := ← requiredField json "base"
      notNull := ← requiredField json "notNull"
      defaultExpr := ← optionalField json "defaultExpr" none
      constraints := ← optionalField json "constraints" #[]
      localConstraints := ← optionalField json "localConstraints" #[]
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
    ("localExpression", toJson value.localExpression),
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
      localExpression := ← optionalField json "localExpression" none
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
    ("logicalType", toJson value.logicalType),
    ("nullable", toJson value.nullable),
    ("origin", toJson value.origin),
    ("collation", toJson value.collation)
  ]

instance : FromJson QueryColumnIR where
  fromJson? json := do
    pure {
      name := ← requiredField json "name"
      ty := ← requiredField json "type"
      logicalType := ← optionalField json "logicalType" none
      nullable := ← requiredField json "nullable"
      origin := ← optionalField json "origin" none
      collation := ← optionalField json "collation" none
    }

instance : ToJson QueryConstraintIR where
  toJson value := Json.mkObj [
    ("relation", toJson value.relation),
    ("name", toJson value.name),
    ("source", toJson value.source),
    ("expression", toJson value.expression),
    ("validated", toJson value.validated)
  ]

instance : FromJson QueryConstraintIR where
  fromJson? json := do
    pure {
      relation := ← requiredField json "relation"
      name := ← requiredField json "name"
      source := ← requiredField json "source"
      expression := ← requiredField json "expression"
      validated := ← optionalField json "validated" true
    }

instance : ToJson QueryIR where
  toJson value := Json.mkObj [
    ("name", toJson value.name),
    ("sql", toJson value.sql),
    ("sqlHash", toJson value.sqlHash),
    ("params", toJson value.params),
    ("columns", toJson value.columns),
    ("localConstraints", toJson value.localConstraints),
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
      localConstraints := ← optionalField json "localConstraints" #[]
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
  let versionFields := [
    ("formatVersion", toJson value.formatVersion),
    ("serverMajor", toJson value.serverMajor)
  ]
  let versionFields :=
    if value.supportedServerMajors.isEmpty then versionFields
    else versionFields ++ [("supportedServerMajors", toJson value.supportedServerMajors)]
  Json.mkObj (versionFields ++ [
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
  ])

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
      supportedServerMajors := ← optionalField json "supportedServerMajors" #[]
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
  if database.formatVersion == 1 || database.formatVersion == 2 then
    pure database.normalize
  else
    throw s!"unsupported Pgx IR format version {database.formatVersion}"

/-- Parse and decode a `.pgir.json` document. -/
def parseSnapshot (document : String) : Except String DatabaseIR := do
  let json ← Json.parse document
  parseSnapshotJson json

end DatabaseIR

end Pgx
