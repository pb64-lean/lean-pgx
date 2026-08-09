import Pgx.IR
import Pg.Types.Codec

namespace Pgx

/-- Information needed by generated code for a built-in PostgreSQL scalar. -/
structure BuiltinTypeMapping where
  key : TypeKey
  leanType : String
  deriving Repr, BEq, Inhabited

private def builtin (name leanType : String) : BuiltinTypeMapping :=
  { key := { schema := "pg_catalog", name, kind := .base }, leanType }

/-- Milestone-1 scalar surface backed by pg-lean codecs.  Arrays, composites,
ranges, and pseudo-types remain hard generation errors. -/
def builtinTypeMappings : Array BuiltinTypeMapping := #[
  builtin "bool" "Bool",
  builtin "bytea" "ByteArray",
  builtin "int2" "Int16",
  builtin "int4" "Int32",
  builtin "int8" "Int64",
  builtin "oid" "Int",
  builtin "float4" "Float",
  builtin "float8" "Float",
  builtin "text" "String",
  builtin "varchar" "String",
  builtin "bpchar" "String",
  builtin "name" "String",
  builtin "char" "String",
  builtin "json" "String",
  builtin "jsonb" "String",
  builtin "uuid" "String",
  builtin "date" "Std.Time.PlainDate",
  builtin "time" "Std.Time.PlainTime",
  builtin "timestamp" "Std.Time.PlainDateTime",
  builtin "timestamptz" "Std.Time.Timestamp",
  builtin "numeric" "Pg.PgNumeric",
  builtin "interval" "Pg.PgInterval"
]

def builtinTypeMapping? (key : TypeKey) : Option BuiltinTypeMapping :=
  builtinTypeMappings.find? (fun mapping => mapping.key == key)

def DatabaseIR.enum? (db : DatabaseIR) (key : TypeKey) : Option EnumIR :=
  db.enums.find? (fun value => value.key == key)

def DatabaseIR.domain? (db : DatabaseIR) (key : TypeKey) : Option DomainIR :=
  db.domains.find? (fun value => value.key == key)

def DatabaseIR.typeOverride? (db : DatabaseIR) (key : TypeKey) : Option TypeOverrideIR :=
  db.typeOverrides.find? (fun value => value.key == key)

inductive TypeSupport where
  | builtin (mapping : BuiltinTypeMapping)
  | enum (value : EnumIR)
  | domain (value : DomainIR)
  | override (value : TypeOverrideIR)
  deriving Repr

def DatabaseIR.typeSupport? (db : DatabaseIR) (key : TypeKey) : Option TypeSupport :=
  match db.typeOverride? key with
  | some value => some (.override value)
  | none =>
    match builtinTypeMapping? key with
    | some value => some (.builtin value)
    | none =>
      match db.enum? key with
      | some value => some (.enum value)
      | none => db.domain? key |>.map .domain

end Pgx
