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
  /-- PostgreSQL 18 added `pg_constraint.conenforced`.  Older supported
  majors enforce every catalog constraint and must not mention the absent
  column in their catalog SQL. -/
  constraintEnforcementCatalog : Bool := false
  /-- PostgreSQL 18 added temporal `PERIOD`/`WITHOUT OVERLAPS` constraints
  and the corresponding `pg_constraint.conperiod` bit. -/
  temporalConstraintCatalog : Bool := false
  deriving Repr, BEq, Inhabited

/-- Version-independent input derived from `pg_attribute.attnotnull`. -/
structure AttributeNotNull where
  relation : Pgx.RelationKey
  column : String
  deriving Repr, BEq, Inhabited

namespace Adapter

def supportsNativeNotNull (adapter : Adapter) : Bool :=
  adapter.notNullCatalog == .nativeConstraint

def supportsConstraintEnforcement (adapter : Adapter) : Bool :=
  adapter.constraintEnforcementCatalog

def supportsTemporalConstraints (adapter : Adapter) : Bool :=
  adapter.temporalConstraintCatalog

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
  let enforced := if adapter.supportsConstraintEnforcement then
    "con.conenforced::text"
  else
    "true::text"
  let period := if adapter.supportsTemporalConstraints then
    "con.conperiod::text"
  else
    "false::text"
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
  ", " ++ enforced ++ ", con.condeferrable::text, con.condeferred::text, " ++
  "pns.nspname, pc.relname, parent.conname, con.conislocal::text, " ++
  "con.coninhcount::text, con.connoinherit::text, " ++ period ++ ", " ++
  "ins.nspname, ic.relname, " ++
  "CASE WHEN con.contype = 'f' THEN con.confmatchtype::text END, " ++
  "CASE WHEN con.contype = 'f' THEN con.confupdtype::text END, " ++
  "CASE WHEN con.contype = 'f' THEN con.confdeltype::text END, " ++
  "COALESCE(i.indnullsnotdistinct, false)::text " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "JOIN pg_catalog.pg_class AS c ON c.oid = con.conrelid " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_class AS rc ON rc.oid = NULLIF(con.confrelid, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rns ON rns.oid = rc.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_constraint AS parent " ++
  "ON parent.oid = NULLIF(con.conparentid, 0) " ++
  "LEFT JOIN pg_catalog.pg_class AS pc ON pc.oid = parent.conrelid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS pns ON pns.oid = pc.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_class AS ic ON ic.oid = NULLIF(con.conindid, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS ins ON ins.oid = ic.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_index AS i ON i.indexrelid = con.conindid " ++
  "WHERE con.conrelid <> 0 AND con.contype IN (" ++
  adapter.constraintTypeList ++ ") ORDER BY con.oid"

/-- Constraint-column query for this server major.  PostgreSQL 18's native
`NOT NULL` rows use `conkey`, just like the other local constraint kinds. -/
def constraintColumnSql (adapter : Adapter) : String :=
  "SELECT con.oid, false::text, key.ordinality, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.conkey) " ++
  "WITH ORDINALITY AS key(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.conrelid AND a.attnum = key.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype IN (" ++
  adapter.constraintTypeList ++ ") UNION ALL " ++
  "SELECT con.oid, true::text, key.ordinality, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.confkey) " ++
  "WITH ORDINALITY AS key(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.confrelid AND a.attnum = key.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype = 'f' ORDER BY 1, 2, 3"

/-- Foreign-key delete-action column subset.  A missing row set represents
the PostgreSQL default of applying `SET NULL`/`SET DEFAULT` to every key
column; an explicitly stored subset retains declaration order. -/
def constraintDeleteSetColumnSql : String :=
  "SELECT con.oid, key.ordinality, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.confdelsetcols) " ++
  "WITH ORDINALITY AS key(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.conrelid AND a.attnum = key.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype = 'f' " ++
  "ORDER BY con.oid, key.ordinality"

/-- Resolved operator vectors whose order is semantic.  OIDs are returned
only to the transient probe, which replaces them with symbolic operator and
operand type identities before constructing `DatabaseIR`. -/
def constraintOperatorSql : String :=
  let branch (field tag : String) :=
    "SELECT con.oid, '" ++ tag ++ "'::text, item.ordinality, " ++
    "op.oid, ons.nspname, op.oprname, op.oprleft, op.oprright " ++
    "FROM pg_catalog.pg_constraint AS con " ++
    "CROSS JOIN LATERAL pg_catalog.unnest(con." ++ field ++ ") " ++
    "WITH ORDINALITY AS item(operator_oid, ordinality) " ++
    "JOIN pg_catalog.pg_operator AS op ON op.oid = item.operator_oid " ++
    "JOIN pg_catalog.pg_namespace AS ons ON ons.oid = op.oprnamespace"
  String.intercalate " UNION ALL " [
    branch "conpfeqop" "pf",
    branch "conppeqop" "pp",
    branch "conffeqop" "ff",
    branch "conexclop" "exclude"
  ] ++ " ORDER BY 1, 2, 3"

private def canonicalNotNull (value : AttributeNotNull)
    (source : Option Pgx.ConstraintIR := none) : Pgx.ConstraintIR :=
  let base : Pgx.ConstraintIR := {
    relation := value.relation
    name := s!"<not-null:{value.column}>"
    kind := .notNull
    columns := #[value.column]
  }
  match source with
  | none => base
  | some source => { base with
      enforced := source.enforced
      validated := source.validated
      parent := source.parent
      isLocal := source.isLocal
      inheritanceCount := source.inheritanceCount
      noInherit := source.noInherit
    }

private def notNullKey (constraint : Pgx.ConstraintIR) : Except String AttributeNotNull := do
  unless constraint.columns.size == 1 do
    throw s!"native NOT NULL constraint {constraint.relation}.{constraint.name} \
      must name exactly one column"
  if constraint.referencedRelation.isSome || !constraint.referencedColumns.isEmpty ||
      constraint.expression.isSome || constraint.localExpression.isSome ||
      constraint.deferrable || constraint.initiallyDeferred || constraint.period ||
      constraint.supportingIndex.isSome ||
      !constraint.foreignKeyDeleteSetColumns.isEmpty ||
      !constraint.referencedToReferencingOperators.isEmpty ||
      !constraint.referencedEqualityOperators.isEmpty ||
      !constraint.referencingEqualityOperators.isEmpty ||
      !constraint.exclusionElements.isEmpty then
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
      unless constraint.enforced && constraint.validated do
        throw s!"native NOT NULL constraint {constraint.relation}.{constraint.name} \
          must be enforced and validated before lean-pgx can treat the column as non-null"
      unless attributes.contains key do
        throw s!"native NOT NULL constraint for {key.relation}.{key.column} \
          is absent from pg_attribute"
      if nativeKeys.contains key then
        throw s!"duplicate native NOT NULL constraint for {key.relation}.{key.column}"
      nativeKeys := nativeKeys.push key
      let normalized := canonicalNotNull key (some constraint)
      if result.any (fun existing => existing.key == normalized.key) then
        throw s!"duplicate normalized constraint identity {normalized.key}"
      result := result.push normalized
    else
      if result.any (fun existing => existing.key == constraint.key) then
        throw s!"duplicate normalized constraint identity {constraint.key}"
      result := result.push constraint
  for key in attributes do
    unless nativeKeys.contains key do
      let normalized := canonicalNotNull key
      if result.any (fun existing => existing.key == normalized.key) then
        throw s!"synthetic NOT NULL identity {normalized.key} collides with a \
          PostgreSQL constraint name"
      result := result.push normalized
  pure result

end Adapter

end Pgx.Codegen.Probe
