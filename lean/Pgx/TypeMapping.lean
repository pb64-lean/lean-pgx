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

/-- Built-in scalar surface backed by pg-lean codecs.  Symbolic container and
composite mappings are resolved from their generated IR records. -/
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

def DatabaseIR.array? (db : DatabaseIR) (key : TypeKey) : Option ArrayIR :=
  db.arrays.find? (fun value => value.key == key)

def DatabaseIR.composite? (db : DatabaseIR) (key : TypeKey) : Option CompositeIR :=
  db.composites.find? (fun value => value.key == key)

def DatabaseIR.range? (db : DatabaseIR) (key : TypeKey) : Option RangeIR :=
  db.ranges.find? (fun value => value.key == key)

def DatabaseIR.multirange? (db : DatabaseIR) (key : TypeKey) : Option MultirangeIR :=
  db.multiranges.find? (fun value => value.key == key)

def DatabaseIR.typeOverride? (db : DatabaseIR) (key : TypeKey) : Option TypeOverrideIR :=
  db.typeOverrides.find? (fun value => value.key == key)

inductive TypeSupport where
  | builtin (mapping : BuiltinTypeMapping)
  | enum (value : EnumIR)
  | domain (value : DomainIR)
  | array (value : ArrayIR)
  | composite (value : CompositeIR)
  | range (value : RangeIR)
  | multirange (value : MultirangeIR)
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
      | none =>
        match db.domain? key with
        | some value => some (.domain value)
        | none =>
          match db.array? key with
          | some value => some (.array value)
          | none =>
            match db.composite? key with
            | some value => some (.composite value)
            | none =>
              match db.range? key with
              | some value => some (.range value)
              | none => db.multirange? key |>.map .multirange

end Pgx
