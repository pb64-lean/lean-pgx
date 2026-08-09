import Pgx.IR

/-!
# Versioned PostgreSQL probe adapters

Catalog layouts are an input to probing, not part of the canonical contract.
An adapter describes the catalog surface for one PostgreSQL major and removes
that surface's representation differences before values reach `DatabaseIR`.
-/

namespace Pgx.Codegen.Probe

/-- Where a server major exposes relation-level `NOT NULL` metadata. -/
inductive NotNullCatalog where
  /-- The constraint is represented only by `pg_attribute.attnotnull`. -/
  | attributeOnly
  /-- The constraint is also represented by a `pg_constraint` row. -/
  | nativeConstraint
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Catalog behavior selected after reading the live server's actual major. -/
structure Adapter where
  serverMajor : Nat
  notNullCatalog : NotNullCatalog
  deriving Repr, BEq, Inhabited

/-- Version-independent input derived from `pg_attribute.attnotnull`. -/
structure AttributeNotNull where
  relation : Pgx.RelationKey
  column : String
  deriving Repr, BEq, Inhabited

namespace Adapter

def supportsNativeNotNull (adapter : Adapter) : Bool :=
  adapter.notNullCatalog == .nativeConstraint

/-- `pg_constraint.contype` tags understood by this adapter. -/
def constraintTypeTags (adapter : Adapter) : Array String :=
  if adapter.supportsNativeNotNull then
    #["c", "n", "p", "u", "f", "x"]
  else
    #["c", "p", "u", "f", "x"]

/-- Convert a version-specific catalog tag into the shared IR kind. -/
def constraintKind? (adapter : Adapter) : String → Option Pgx.ConstraintKind
  | "c" => some .check
  | "n" => if adapter.supportsNativeNotNull then some .notNull else none
  | "p" => some .primaryKey
  | "u" => some .unique
  | "f" => some .foreignKey
  | "x" => some .exclusion
  | _ => none

private def constraintTypeList (adapter : Adapter) : String :=
  String.intercalate ", "
    (adapter.constraintTypeTags.toList.map fun tag => "'" ++ tag ++ "'")

/-- Relation-constraint query for this server major. -/
def constraintCatalogSql (adapter : Adapter) : String :=
  "SELECT con.oid::text, ns.nspname, c.relname, con.conname, con.contype::text, " ++
  "rns.nspname, rc.relname, " ++
  "CASE WHEN con.contype IN ('c', 'x') " ++
  "THEN pg_catalog.pg_get_constraintdef(con.oid, true) ELSE NULL END, " ++
  "con.convalidated::text, " ++
  "(EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
  "WHERE dep.classid = 'pg_catalog.pg_constraint'::pg_catalog.regclass " ++
  "AND dep.objid = con.oid " ++
  "AND dep.refclassid = 'pg_catalog.pg_proc'::pg_catalog.regclass))::text, " ++
  "(EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
  "WHERE dep.classid = 'pg_catalog.pg_constraint'::pg_catalog.regclass " ++
  "AND dep.objid = con.oid " ++
  "AND dep.refclassid = 'pg_catalog.pg_operator'::pg_catalog.regclass))::text " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "JOIN pg_catalog.pg_class AS c ON c.oid = con.conrelid " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_class AS rc ON rc.oid = NULLIF(con.confrelid, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rns ON rns.oid = rc.relnamespace " ++
  "WHERE con.conrelid <> 0 AND con.contype IN (" ++
  adapter.constraintTypeList ++ ") ORDER BY con.oid"

/-- Constraint-column query for this server major.  PostgreSQL 18's native
`NOT NULL` rows use `conkey`, just like the other local constraint kinds. -/
def constraintColumnSql (adapter : Adapter) : String :=
  "SELECT con.oid::text, false::text, key.ordinality::text, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.conkey) " ++
  "WITH ORDINALITY AS key(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.conrelid AND a.attnum = key.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype IN (" ++
  adapter.constraintTypeList ++ ") UNION ALL " ++
  "SELECT con.oid::text, true::text, key.ordinality::text, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.confkey) " ++
  "WITH ORDINALITY AS key(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.confrelid AND a.attnum = key.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype = 'f' ORDER BY 1, 2, 3"

private def canonicalNotNull (value : AttributeNotNull)
    (validated : Bool := true) : Pgx.ConstraintIR := {
  relation := value.relation
  name := s!"<not-null:{value.column}>"
  kind := .notNull
  columns := #[value.column]
  validated
}

private def notNullKey (constraint : Pgx.ConstraintIR) : Except String AttributeNotNull := do
  unless constraint.columns.size == 1 do
    throw s!"native NOT NULL constraint {constraint.relation}.{constraint.name} \
      must name exactly one column"
  if constraint.referencedRelation.isSome || !constraint.referencedColumns.isEmpty ||
      constraint.expression.isSome then
    throw s!"native NOT NULL constraint {constraint.relation}.{constraint.name} \
      has unexpected catalog metadata"
  pure { relation := constraint.relation, column := constraint.columns[0]! }

/-- Normalize relation constraints into the PostgreSQL-17 shape.  PostgreSQL
18's native `NOT NULL` name and catalog row are deliberately replaced by the
same stable synthetic identity derived from `pg_attribute` on PostgreSQL 17.
Attribute rows not backed by a native row (for example, implicit primary-key
nullability) are added on both majors. -/
def normalizeConstraints (adapter : Adapter)
    (catalog : Array Pgx.ConstraintIR)
    (attributes : Array AttributeNotNull) : Except String (Array Pgx.ConstraintIR) := do
  let mut result : Array Pgx.ConstraintIR := #[]
  let mut nativeKeys : Array AttributeNotNull := #[]
  for constraint in catalog do
    if constraint.kind == .notNull then
      unless adapter.supportsNativeNotNull do
        throw s!"PostgreSQL {adapter.serverMajor} adapter received a native NOT NULL constraint"
      let key ← notNullKey constraint
      unless attributes.contains key do
        throw s!"native NOT NULL constraint for {key.relation}.{key.column} \
          is absent from pg_attribute"
      if nativeKeys.contains key then
        throw s!"duplicate native NOT NULL constraint for {key.relation}.{key.column}"
      nativeKeys := nativeKeys.push key
      result := result.push (canonicalNotNull key constraint.validated)
    else
      result := result.push constraint
  for key in attributes do
    unless nativeKeys.contains key do
      result := result.push (canonicalNotNull key)
  pure result

end Adapter

end Pgx.Codegen.Probe
