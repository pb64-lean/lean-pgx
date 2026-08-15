module

public import Pgx.Typed.Descriptors
public import Pg.Connection

public section

/-!
# Live catalog attachment

This module turns a raw PostgreSQL connection into a capability tied to a
generated `DatabaseDesc`.  Installation-local OIDs are read only here: all
comparisons are made against symbolic type and relation keys before the
resolved values are exposed to generated query code.
-/

namespace Pgx.Typed

open Std.Async

private def drift (message : String) : Error :=
  .schemaDrift message

private def sqlLiteral (value : String) : String :=
  "'" ++ value.replace "'" "''" ++ "'"

private def sqlIdentifier (value : String) : String :=
  "\"" ++ value.replace "\"" "\"\"" ++ "\""

private def queryOne (conn : Pg.Connection) (context sql : String) :
    Async (Except Error Pg.Rows) := do
  match ← Pg.Connection.query conn sql with
  | .error error => pure (.error (.postgres error))
  | .ok results =>
    match results with
    | #[rows] => pure (.ok rows)
    | _ => pure (.error (drift
        s!"{context}: expected one result set, received {results.size}"))

private def cell? (context : String) (row : Array (Option ByteArray))
    (index : Nat) : Except Error (Option String) := do
  let some value := row[index]?
    | throw (drift s!"{context}: result row has no column {index}")
  match value with
  | none => pure none
  | some bytes =>
    let some value := String.fromUTF8? bytes
      | throw (drift s!"{context}: result column {index} is not UTF-8")
    pure (some value)

private def cell (context : String) (row : Array (Option ByteArray))
    (index : Nat) : Except Error String := do
  let some value ← cell? context row index
    | throw (drift s!"{context}: result column {index} is NULL")
  pure value

private def parseNat (context value : String) : Except Error Nat := do
  let some parsed := value.toNat?
    | throw (drift s!"{context}: expected an unsigned integer, received {value}")
  pure parsed

private def parseUInt32 (context value : String) : Except Error UInt32 := do
  let parsed ← parseNat context value
  if parsed < 4294967296 then
    pure (UInt32.ofNat parsed)
  else
    throw (drift s!"{context}: value is outside the UInt32 range: {value}")

private def parseUInt16 (context value : String) : Except Error UInt16 := do
  let parsed ← parseNat context value
  if parsed < 65536 then
    pure (UInt16.ofNat parsed)
  else
    throw (drift s!"{context}: value is outside the UInt16 range: {value}")

private def parseInt32 (context value : String) : Except Error Int32 := do
  let some parsed := value.toInt?
    | throw (drift s!"{context}: expected an integer, received {value}")
  if (-2147483648 : Int) ≤ parsed ∧ parsed ≤ 2147483647 then
    pure (Int32.ofInt parsed)
  else
    throw (drift s!"{context}: value is outside the Int32 range: {value}")

private def parseBool (context value : String) : Except Error Bool :=
  match value with
  | "t" | "true" | "on" => pure true
  | "f" | "false" | "off" => pure false
  | _ => throw (drift s!"{context}: expected a boolean, received {value}")

private def parseConstraintKind (context : String) : String →
    Except Error Pgx.ConstraintKind
  | "c" => pure .check
  | "n" => pure .notNull
  | "p" => pure .primaryKey
  | "u" => pure .unique
  | "f" => pure .foreignKey
  | "x" => pure .exclusion
  | value => throw (drift s!"{context}: unknown PostgreSQL constraint kind {value}")

private def parseForeignKeyMatch (context : String) : String →
    Except Error Pgx.ForeignKeyMatch
  | "s" => pure .simple
  | "f" => pure .full
  | "p" => pure .partialMatch
  | value => throw (drift s!"{context}: unknown foreign-key match type {value}")

private def parseForeignKeyAction (context : String) : String →
    Except Error Pgx.ForeignKeyAction
  | "a" => pure .noAction
  | "r" => pure .restrict
  | "c" => pure .cascade
  | "n" => pure .setNull
  | "d" => pure .setDefault
  | value => throw (drift s!"{context}: unknown foreign-key action {value}")

private def parseTypeKind (context : String) : String → Except Error Pgx.TypeKind
  | "base" => pure .base
  | "enum" => pure .enum
  | "domain" => pure .domain
  | "array" => pure .array
  | "range" => pure .range
  | "multirange" => pure .multirange
  | "composite" => pure .composite
  | "pseudo" => pure .pseudo
  | value => throw (drift s!"{context}: unknown PostgreSQL type kind {value}")

private def parseRelationKind (context : String) : String → Except Error Pgx.RelationKind
  | "r" => pure .table
  | "p" => pure .partitionedTable
  | "v" => pure .view
  | "m" => pure .materializedView
  | "f" => pure .foreignTable
  | value => throw (drift s!"{context}: unknown PostgreSQL relation kind {value}")

private def parseRoutineKind (context : String) : String → Except Error Pgx.RoutineKind
  | "f" => pure .function
  | "p" => pure .procedure
  | "a" => pure .aggregate
  | "w" => pure .window
  | value => throw (drift s!"{context}: unknown PostgreSQL routine kind {value}")

private def parseRoutineArgMode (context : String) : String →
    Except Error Pgx.RoutineArgMode
  | "i" => pure .input
  | "o" => pure .output
  | "b" => pure .inputOutput
  | "v" => pure .variadic
  | "t" => pure .table
  | value => throw (drift s!"{context}: unknown PostgreSQL routine argument mode {value}")

private def parseViewCheckOption (context : String) : String →
    Except Error Pgx.ViewCheckOption
  | "none" => pure .none
  | "local" => pure .local
  | "cascaded" => pure .cascaded
  | value => throw (drift s!"{context}: unknown view check option {value}")

private def setConfig (conn : Pg.Connection) (name value : String) :
    Async (Except Error Unit) := do
  let sql := s!"SELECT pg_catalog.set_config({sqlLiteral name}, {sqlLiteral value}, false)"
  match ← queryOne conn s!"install session setting {name}" sql with
  | .error error => pure (.error error)
  | .ok rows =>
    if rows.rows.size == 1 then pure (.ok ())
    else pure (.error (drift
      s!"install session setting {name}: expected one row, received {rows.rows.size}"))

private def currentSetting (conn : Pg.Connection) (name : String) :
    Async (Except Error String) := do
  let sql := s!"SELECT pg_catalog.current_setting({sqlLiteral name})"
  match ← queryOne conn s!"read session setting {name}" sql with
  | .error error => pure (.error error)
  | .ok rows =>
    let some row := rows.rows[0]?
      | return .error (drift s!"read session setting {name}: no row returned")
    if rows.rows.size != 1 then
      return .error (drift
        s!"read session setting {name}: expected one row, received {rows.rows.size}")
    pure (cell s!"read session setting {name}" row 0)

private def validateServerMajor (db : DatabaseDesc) (conn : Pg.Connection) :
    Async (Except Error Nat) := do
  match ← currentSetting conn "server_version_num" with
  | .error error => pure (.error error)
  | .ok version =>
    match parseNat "server_version_num" version with
    | .error error => pure (.error error)
    | .ok versionNumber =>
      let major := versionNumber / 10000
      if major != 17 && major != 18 then
        pure (.error (drift
          s!"unsupported PostgreSQL server major {major}; this runtime understands only 17 and 18"))
      else if db.serverMajors.contains major then
        pure (.ok major)
      else
        pure (.error (drift
          s!"unsupported PostgreSQL server major {major}; expected one of {repr db.serverMajors}"))

private def installSession (db : DatabaseDesc) (conn : Pg.Connection) :
    Async (Except Error Unit) := do
  -- The catalog protocol and generated codecs require UTF-8.  Refuse a
  -- descriptor that would make the next server response undecodable.
  unless db.session.encoding.toUpper == "UTF8" do
    return .error (drift
      s!"unsupported client encoding in generated contract: {db.session.encoding}")
  let searchPath := String.intercalate ", "
    (db.session.searchPath.map sqlIdentifier).toList
  match ← setConfig conn "search_path" searchPath with
  | .error error => return .error error
  | .ok () => pure ()
  match ← setConfig conn "TimeZone" db.session.timezone with
  | .error error => return .error error
  | .ok () => pure ()
  match ← setConfig conn "client_encoding" db.session.encoding with
  | .error error => return .error error
  | .ok () => pure ()
  match ← setConfig conn "standard_conforming_strings"
      (if db.session.standardConformingStrings then "on" else "off") with
  | .error error => return .error error
  | .ok () => pure ()

  match ← currentSetting conn "TimeZone" with
  | .error error => return .error error
  | .ok actual =>
    unless actual == db.session.timezone do
      return .error (drift
        s!"session TimeZone drift: expected {db.session.timezone}, received {actual}")
  match ← currentSetting conn "client_encoding" with
  | .error error => return .error error
  | .ok actual =>
    unless actual.toUpper == db.session.encoding.toUpper do
      return .error (drift
        s!"session client_encoding drift: expected {db.session.encoding}, received {actual}")
  match ← currentSetting conn "standard_conforming_strings" with
  | .error error => return .error error
  | .ok actual =>
    match parseBool "standard_conforming_strings" actual with
    | .error error => return .error error
    | .ok value =>
      unless value == db.session.standardConformingStrings do
        return .error (drift
          s!"session standard_conforming_strings drift: expected \
            {db.session.standardConformingStrings}, received {actual}")

  match ← queryOne conn "read effective search_path"
      "SELECT schema_name FROM pg_catalog.unnest(pg_catalog.current_schemas(false)) \
       WITH ORDINALITY AS path(schema_name, ordinal) ORDER BY ordinal" with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut actual : Array String := #[]
    for row in rows.rows do
      match cell "read effective search_path" row 0 with
      | .error error => return .error error
      | .ok schema => actual := actual.push schema
    if actual == db.session.searchPath then
      pure (.ok ())
    else
      pure (.error (drift
        s!"effective search_path drift: expected {repr db.session.searchPath}, received {repr actual}"))

private structure LiveType where
  key : Pgx.TypeKey
  oid : UInt32
  arrayOid : Option UInt32
  base : Option Pgx.TypeRef
  enumLabels : Array String := #[]
  notNull : Bool
  arrayElement : Option Pgx.TypeRef := none
  arrayDelimiter : Option String := none
  compositeFields : Array Pgx.CompositeFieldIR := #[]
  rangeSubtype : Option Pgx.TypeRef := none
  rangeMultirange : Option Pgx.TypeKey := none
  rangeCollation : Option Pgx.CollationKey := none
  rangeSubtypeOpclass : Option Pgx.QualifiedName := none
  rangeCanonical : Option Pgx.RoutineKey := none
  rangeSubtypeDiff : Option Pgx.RoutineKey := none
  multirangeRange : Option Pgx.TypeKey := none

private def kindSql (alias : String) : String :=
  s!"CASE WHEN {alias}.typcategory = 'A' AND {alias}.typelem <> 0 \
     AND {alias}.typinput = 'pg_catalog.array_in'::pg_catalog.regproc \
     AND {alias}.typoutput = 'pg_catalog.array_out'::pg_catalog.regproc \
     AND {alias}.typreceive = 'pg_catalog.array_recv'::pg_catalog.regproc \
     AND {alias}.typsend = 'pg_catalog.array_send'::pg_catalog.regproc THEN 'array' \
     WHEN {alias}.typtype = 'b' THEN 'base' \
     WHEN {alias}.typtype = 'c' THEN 'composite' \
     WHEN {alias}.typtype = 'd' THEN 'domain' \
     WHEN {alias}.typtype = 'e' THEN 'enum' \
     WHEN {alias}.typtype = 'p' THEN 'pseudo' \
     WHEN {alias}.typtype = 'r' THEN 'range' \
     WHEN {alias}.typtype = 'm' THEN 'multirange' ELSE 'pseudo' END"

private def typeCatalogSql : String :=
  "SELECT ns.nspname, t.typname, " ++ kindSql "t" ++
  ", t.oid::text, NULLIF(t.typarray, 0)::text, " ++
  "bns.nspname, bt.typname, CASE WHEN bt.oid IS NULL THEN NULL ELSE " ++
  kindSql "bt" ++ " END, " ++
  "CASE WHEN t.typtype = 'd' AND t.typtypmod <> -1 THEN t.typtypmod::text ELSE NULL END, " ++
  "t.typnotnull::text, ens.nspname, et.typname, " ++
  "CASE WHEN et.oid IS NULL THEN NULL ELSE " ++ kindSql "et" ++ " END, " ++
  "CASE WHEN et.oid IS NULL THEN NULL ELSE t.typdelim::text END, " ++
  "rsns.nspname, rst.typname, CASE WHEN rst.oid IS NULL THEN NULL ELSE " ++
  kindSql "rst" ++ " END, rmns.nspname, rmt.typname, " ++
  "CASE WHEN rmt.oid IS NULL THEN NULL ELSE " ++ kindSql "rmt" ++ " END, " ++
  "rrns.nspname, rrt.typname, CASE WHEN rrt.oid IS NULL THEN NULL ELSE " ++
  kindSql "rrt" ++ " END, " ++
  "rcns.nspname, rc.collname, ropns.nspname, rop.opcname, " ++
  "rcanns.nspname, rcan.proname, rdns.nspname, rdiff.proname " ++
  "FROM pg_catalog.pg_type AS t " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = t.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_type AS bt ON bt.oid = NULLIF(t.typbasetype, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS bns ON bns.oid = bt.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_type AS et ON et.oid = NULLIF(t.typelem, 0) " ++
  "AND t.typcategory = 'A' " ++
  "LEFT JOIN pg_catalog.pg_namespace AS ens ON ens.oid = et.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_range AS rg ON rg.rngtypid = t.oid " ++
  "LEFT JOIN pg_catalog.pg_type AS rst ON rst.oid = rg.rngsubtype " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rsns ON rsns.oid = rst.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_type AS rmt ON rmt.oid = rg.rngmultitypid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rmns ON rmns.oid = rmt.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_range AS mrg ON mrg.rngmultitypid = t.oid " ++
  "LEFT JOIN pg_catalog.pg_type AS rrt ON rrt.oid = mrg.rngtypid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rrns ON rrns.oid = rrt.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_collation AS rc ON rc.oid = NULLIF(rg.rngcollation, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rcns ON rcns.oid = rc.collnamespace " ++
  "LEFT JOIN pg_catalog.pg_opclass AS rop ON rop.oid = rg.rngsubopc " ++
  "LEFT JOIN pg_catalog.pg_namespace AS ropns ON ropns.oid = rop.opcnamespace " ++
  "LEFT JOIN pg_catalog.pg_proc AS rcan ON rcan.oid = NULLIF(rg.rngcanonical, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rcanns ON rcanns.oid = rcan.pronamespace " ++
  "LEFT JOIN pg_catalog.pg_proc AS rdiff ON rdiff.oid = NULLIF(rg.rngsubdiff, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rdns ON rdns.oid = rdiff.pronamespace " ++
  "ORDER BY ns.nspname, t.typname"

private def enumCatalogSql : String :=
  "SELECT ns.nspname, t.typname, e.enumlabel " ++
  "FROM pg_catalog.pg_type AS t " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = t.typnamespace " ++
  "JOIN pg_catalog.pg_enum AS e ON e.enumtypid = t.oid " ++
  "ORDER BY ns.nspname, t.typname, e.enumsortorder"

private def compositeCatalogSql : String :=
  "SELECT ns.nspname, t.typname, a.attname, a.attnum::text, " ++
  "fns.nspname, ft.typname, " ++ kindSql "ft" ++ ", " ++
  "CASE WHEN a.atttypmod = -1 THEN NULL ELSE a.atttypmod::text END, " ++
  "cns.nspname, coll.collname " ++
  "FROM pg_catalog.pg_type AS t " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = t.typnamespace " ++
  "JOIN pg_catalog.pg_class AS c ON c.oid = t.typrelid AND c.reltype = t.oid " ++
  "JOIN pg_catalog.pg_attribute AS a ON a.attrelid = c.oid " ++
  "JOIN pg_catalog.pg_type AS ft ON ft.oid = a.atttypid " ++
  "JOIN pg_catalog.pg_namespace AS fns ON fns.oid = ft.typnamespace " ++
  "LEFT JOIN pg_catalog.pg_collation AS coll ON coll.oid = NULLIF(a.attcollation, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS cns ON cns.oid = coll.collnamespace " ++
  "WHERE t.typtype = 'c' AND t.typisdefined " ++
  "AND a.attnum > 0 AND NOT a.attisdropped " ++
  "ORDER BY ns.nspname, t.typname, a.attnum"

private def optionalTypeRef (context : String) (row : Array (Option ByteArray))
    (offset : Nat) : Except Error (Option Pgx.TypeRef) := do
  let schema ← cell? context row offset
  let name ← cell? context row (offset + 1)
  let kind ← cell? context row (offset + 2)
  match schema, name, kind with
  | none, none, none => pure none
  | some schema, some name, some kind =>
    pure (some { key := { schema, name, kind := ← parseTypeKind context kind } })
  | _, _, _ => throw (drift s!"{context}: incomplete component type identity")

private def optionalQualifiedName (context identity : String)
    (row : Array (Option ByteArray)) (offset : Nat) :
    Except Error (Option Pgx.QualifiedName) := do
  let schema ← cell? context row offset
  let name ← cell? context row (offset + 1)
  match schema, name with
  | none, none => pure none
  | some schema, some name => pure (some { schema, name })
  | _, _ => throw (drift s!"{context}: incomplete {identity} identity")

private def parseLiveType (row : Array (Option ByteArray)) : Except Error LiveType := do
  let context := "read pg_type"
  let schema ← cell context row 0
  let name ← cell context row 1
  let kind ← parseTypeKind context (← cell context row 2)
  let oid ← parseUInt32 context (← cell context row 3)
  let arrayOid ← match ← cell? context row 4 with
    | none => pure none
    | some value => some <$> parseUInt32 context value
  let baseSchema ← cell? context row 5
  let baseName ← cell? context row 6
  let baseKind ← cell? context row 7
  let baseTypmod ← match ← cell? context row 8 with
    | none => pure none
    | some value => some <$> parseInt32 context value
  let base ← match baseSchema, baseName, baseKind with
    | none, none, none =>
      if baseTypmod.isNone then pure none
      else throw (drift s!"{context}: base typmod exists without a base type")
    | some schema, some name, some kind =>
      pure (some {
        key := { schema, name, kind := ← parseTypeKind context kind }
        typmod := baseTypmod
      })
    | _, _, _ => throw (drift s!"{context}: incomplete domain base identity")
  let notNull ← parseBool context (← cell context row 9)
  let arrayElement ← optionalTypeRef context row 10
  let arrayDelimiter ← cell? context row 13
  if arrayElement.isSome != arrayDelimiter.isSome then
    throw (drift s!"{context}: incomplete array component metadata for {schema}.{name}")
  let rangeSubtype ← optionalTypeRef context row 14
  let rangeMultirange := (← optionalTypeRef context row 17).map (·.key)
  let multirangeRange := (← optionalTypeRef context row 20).map (·.key)
  let rangeCollation := (← optionalQualifiedName context "range collation" row 23).map fun value =>
    ({ schema := value.schema, name := value.name } : Pgx.CollationKey)
  let rangeSubtypeOpclass ←
    optionalQualifiedName context "range subtype opclass" row 25
  let rangeCanonical := (←
      optionalQualifiedName context "range canonical routine" row 27).map fun value => {
    schema := value.schema
    name := value.name
    inputTypes := #[{ key := { schema, name, kind } }]
  }
  let rangeSubtypeDiff ← match ←
      optionalQualifiedName context "range subtype-diff routine" row 29 with
    | none => pure none
    | some value =>
        let some subtype := rangeSubtype
          | throw (drift s!"{context}: range subtype-diff exists without a subtype")
        pure (some {
          schema := value.schema
          name := value.name
          inputTypes := #[subtype, subtype]
        })
  if kind == .range then
    unless rangeSubtype.isSome && rangeMultirange.isSome &&
        rangeSubtypeOpclass.isSome do
      throw (drift s!"{context}: incomplete range metadata for {schema}.{name}")
    unless multirangeRange.isNone do
      throw (drift s!"{context}: range {schema}.{name} carries multirange metadata")
  else if kind == .multirange then
    unless multirangeRange.isSome do
      throw (drift s!"{context}: incomplete multirange metadata for {schema}.{name}")
    unless rangeSubtype.isNone && rangeMultirange.isNone && rangeCollation.isNone &&
        rangeSubtypeOpclass.isNone && rangeCanonical.isNone && rangeSubtypeDiff.isNone do
      throw (drift s!"{context}: multirange {schema}.{name} carries range metadata")
  else
    unless rangeSubtype.isNone && rangeMultirange.isNone && rangeCollation.isNone &&
        rangeSubtypeOpclass.isNone && rangeCanonical.isNone && rangeSubtypeDiff.isNone &&
        multirangeRange.isNone do
      throw (drift s!"{context}: non-range type {schema}.{name} carries range metadata")
  pure {
    key := { schema, name, kind }, oid, arrayOid, base, notNull,
    arrayElement, arrayDelimiter, rangeSubtype, rangeMultirange,
    rangeCollation, rangeSubtypeOpclass, rangeCanonical, rangeSubtypeDiff,
    multirangeRange
  }

private def loadTypes (conn : Pg.Connection) :
    Async (Except Error (Array LiveType)) := do
  match ← queryOne conn "read pg_type" typeCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut types : Array LiveType := #[]
    for row in rows.rows do
      match parseLiveType row with
      | .error error => return .error error
      | .ok value => types := types.push value
    match ← queryOne conn "read pg_enum" enumCatalogSql with
    | .error error => pure (.error error)
    | .ok enumRows =>
      for row in enumRows.rows do
        let parsed : Except Error (String × String × String) := do
          pure (← cell "read pg_enum" row 0,
            ← cell "read pg_enum" row 1,
            ← cell "read pg_enum" row 2)
        match parsed with
        | .error error => return .error error
        | .ok (schema, name, label) =>
          let key : Pgx.TypeKey := { schema, name, kind := .enum }
          let some index := types.findIdx? (fun value => value.key == key)
            | return .error (drift s!"pg_enum refers to missing type {key}")
          let some value := types[index]?
            | return .error (drift s!"pg_enum type index disappeared for {key}")
          types := types.set! index { value with enumLabels := value.enumLabels.push label }
      match ← queryOne conn "read composite pg_attribute" compositeCatalogSql with
      | .error error => pure (.error error)
      | .ok compositeRows =>
        for row in compositeRows.rows do
          let parsed : Except Error (Pgx.TypeKey × Pgx.CompositeFieldIR) := do
            let ownerSchema ← cell "read composite pg_attribute" row 0
            let ownerName ← cell "read composite pg_attribute" row 1
            let name ← cell "read composite pg_attribute" row 2
            let ordinal ← parseNat "read composite pg_attribute"
              (← cell "read composite pg_attribute" row 3)
            let typeSchema ← cell "read composite pg_attribute" row 4
            let typeName ← cell "read composite pg_attribute" row 5
            let typeKind ← parseTypeKind "read composite pg_attribute"
              (← cell "read composite pg_attribute" row 6)
            let typmod ← match ← cell? "read composite pg_attribute" row 7 with
              | none => pure none
              | some value => some <$> parseInt32 "read composite pg_attribute" value
            let collationSchema ← cell? "read composite pg_attribute" row 8
            let collationName ← cell? "read composite pg_attribute" row 9
            let collation ← match collationSchema, collationName with
              | none, none => pure none
              | some schema, some name => pure (some { schema, name })
              | _, _ => throw (drift
                  "read composite pg_attribute: incomplete collation identity")
            pure ({ schema := ownerSchema, name := ownerName, kind := .composite }, {
              name, ordinal
              ty := { key := { schema := typeSchema, name := typeName, kind := typeKind }, typmod }
              collation
            })
          match parsed with
          | .error error => return .error error
          | .ok (key, field) =>
            let some index := types.findIdx? (fun value => value.key == key)
              | return .error (drift s!"composite field refers to missing type {key}")
            let some value := types[index]?
              | return .error (drift s!"composite type index disappeared for {key}")
            types := types.set! index {
              value with compositeFields := value.compositeFields.push field
            }
        pure (.ok types)

private structure LiveColumn where
  name : String
  attnum : UInt16
  ty : Pgx.TypeRef
  nullable : Bool
  /-- Relation-level nullability before a domain's own NOT NULL bit is
  folded into `nullable`.  This is the cross-version source for canonical
  relation NOT NULL constraints. -/
  attributeNotNull : Bool

private structure LiveRelation where
  key : Pgx.RelationKey
  kind : Pgx.RelationKind
  oid : UInt32
  columns : Array LiveColumn := #[]

private def relationCatalogSql : String :=
  "SELECT ns.nspname, c.relname, c.relkind::text, c.oid::text " ++
  "FROM pg_catalog.pg_class AS c " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "WHERE c.relkind IN ('r', 'p', 'v', 'm', 'f') " ++
  "ORDER BY ns.nspname, c.relname"

private def columnCatalogSql : String :=
  "SELECT ns.nspname, c.relname, a.attname, a.attnum::text, " ++
  "tns.nspname, t.typname, " ++ kindSql "t" ++ ", " ++
  "CASE WHEN a.atttypmod = -1 THEN NULL ELSE a.atttypmod::text END, " ++
  "(NOT (a.attnotnull OR t.typnotnull))::text, a.attnotnull::text " ++
  "FROM pg_catalog.pg_class AS c " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "JOIN pg_catalog.pg_attribute AS a ON a.attrelid = c.oid " ++
  "JOIN pg_catalog.pg_type AS t ON t.oid = a.atttypid " ++
  "JOIN pg_catalog.pg_namespace AS tns ON tns.oid = t.typnamespace " ++
  "WHERE c.relkind IN ('r', 'p', 'v', 'm', 'f') " ++
  "AND a.attnum > 0 AND NOT a.attisdropped " ++
  "ORDER BY ns.nspname, c.relname, a.attnum"

private def parseLiveRelation (row : Array (Option ByteArray)) :
    Except Error LiveRelation := do
  let context := "read pg_class"
  let schema ← cell context row 0
  let name ← cell context row 1
  let kind ← parseRelationKind context (← cell context row 2)
  let oid ← parseUInt32 context (← cell context row 3)
  pure { key := { schema, name }, kind, oid }

private def parseLiveColumn (row : Array (Option ByteArray)) :
    Except Error (Pgx.RelationKey × LiveColumn) := do
  let context := "read pg_attribute"
  let relationSchema ← cell context row 0
  let relationName ← cell context row 1
  let name ← cell context row 2
  let attnum ← parseUInt16 context (← cell context row 3)
  let typeSchema ← cell context row 4
  let typeName ← cell context row 5
  let typeKind ← parseTypeKind context (← cell context row 6)
  let typmod ← match ← cell? context row 7 with
    | none => pure none
    | some value => some <$> parseInt32 context value
  let nullable ← parseBool context (← cell context row 8)
  let attributeNotNull ← parseBool context (← cell context row 9)
  pure ({ schema := relationSchema, name := relationName }, {
    name, attnum, ty := { key := { schema := typeSchema, name := typeName, kind := typeKind }, typmod },
    nullable, attributeNotNull
  })

private def loadRelations (conn : Pg.Connection) :
    Async (Except Error (Array LiveRelation)) := do
  match ← queryOne conn "read pg_class" relationCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut relations : Array LiveRelation := #[]
    for row in rows.rows do
      match parseLiveRelation row with
      | .error error => return .error error
      | .ok value => relations := relations.push value
    match ← queryOne conn "read pg_attribute" columnCatalogSql with
    | .error error => pure (.error error)
    | .ok columnRows =>
      for row in columnRows.rows do
        match parseLiveColumn row with
        | .error error => return .error error
        | .ok (key, column) =>
          let some index := relations.findIdx? (fun value => value.key == key)
            | return .error (drift s!"pg_attribute refers to missing relation {key}")
          let some relation := relations[index]?
            | return .error (drift s!"pg_attribute relation index disappeared for {key}")
          relations := relations.set! index {
            relation with columns := relation.columns.push column
          }
      pure (.ok relations)

private def liveTypeRefByOid (types : Array LiveType) (context : String)
    (oid : UInt32) : Except Error Pgx.TypeRef := do
  let candidates := types.filter (fun value => value.oid == oid)
  let some ty := candidates[0]?
    | throw (drift s!"{context}: PostgreSQL type OID {oid} is missing")
  unless candidates.size == 1 do
    throw (drift s!"{context}: PostgreSQL type OID {oid} is ambiguous")
  pure { key := ty.key }

private def operatorKeyByOperandOids (types : Array LiveType) (context schema name : String)
    (leftOid rightOid : UInt32) : Except Error Pgx.OperatorKey := do
  let leftType := (← liveTypeRefByOid types context leftOid).key
  let rightType := (← liveTypeRefByOid types context rightOid).key
  pure { schema, name, leftType, rightType }

/-! ## Relational constraint and index catalogs

These queries intentionally recover symbolic identities rather than retaining
installation-local OIDs.  The OIDs only join the several catalog result sets
during attachment.
-/

namespace Internal

/-- Semantic index metadata used by relational constraints. -/
def relationalIndexCatalogSql : String :=
  "SELECT i.indexrelid::text, ns.nspname, c.relname, ins.nspname, ic.relname, " ++
  "i.indisunique::text, i.indisprimary::text, i.indisexclusion::text, " ++
  "i.indimmediate::text, i.indisvalid::text, i.indisready::text, " ++
  "i.indislive::text, i.indnullsnotdistinct::text, am.amname, " ++
  "pg_catalog.pg_get_expr(i.indpred, i.indrelid, true), " ++
  "pg_catalog.pg_get_expr(i.indexprs, i.indrelid, true) " ++
  "FROM pg_catalog.pg_index AS i " ++
  "JOIN pg_catalog.pg_class AS c ON c.oid = i.indrelid " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "JOIN pg_catalog.pg_class AS ic ON ic.oid = i.indexrelid " ++
  "JOIN pg_catalog.pg_namespace AS ins ON ins.oid = ic.relnamespace " ++
  "JOIN pg_catalog.pg_am AS am ON am.oid = ic.relam " ++
  "ORDER BY i.indexrelid"

/-- Ordered key and INCLUDE elements.  For btree/hash key elements the
operator-family equality member is resolved to a symbolic operator overload.
-/
def relationalIndexElementSql : String :=
  "SELECT i.indexrelid::text, item.ordinality::text, " ++
  "(item.ordinality <= i.indnkeyatts)::text, a.attname, " ++
  "CASE WHEN item.attnum = 0 THEN " ++
  "pg_catalog.pg_get_indexdef(i.indexrelid, item.ordinality::integer, true) END, " ++
  "cns.nspname, coll.collname, ons.nspname, opc.opcname, " ++
  "((COALESCE(opt.value, 0) & 1) <> 0)::text, " ++
  "((COALESCE(opt.value, 0) & 2) <> 0)::text, " ++
  "eq.operator_schema, eq.operator_name, eq.left_type::text, eq.right_type::text " ++
  "FROM pg_catalog.pg_index AS i " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(i.indkey) " ++
  "WITH ORDINALITY AS item(attnum, ordinality) " ++
  "LEFT JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = i.indrelid AND a.attnum = item.attnum " ++
  "LEFT JOIN LATERAL pg_catalog.unnest(i.indcollation) " ++
  "WITH ORDINALITY AS coll_item(oid, ordinality) " ++
  "ON coll_item.ordinality = item.ordinality " ++
  "LEFT JOIN pg_catalog.pg_collation AS coll ON coll.oid = coll_item.oid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS cns ON cns.oid = coll.collnamespace " ++
  "LEFT JOIN LATERAL pg_catalog.unnest(i.indclass) " ++
  "WITH ORDINALITY AS opclass(oid, ordinality) " ++
  "ON opclass.ordinality = item.ordinality " ++
  "LEFT JOIN pg_catalog.pg_opclass AS opc ON opc.oid = opclass.oid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS ons ON ons.oid = opc.opcnamespace " ++
  "LEFT JOIN LATERAL pg_catalog.unnest(i.indoption) " ++
  "WITH ORDINALITY AS opt(value, ordinality) " ++
  "ON opt.ordinality = item.ordinality " ++
  "LEFT JOIN pg_catalog.pg_class AS ic ON ic.oid = i.indexrelid " ++
  "LEFT JOIN pg_catalog.pg_am AS iam ON iam.oid = ic.relam " ++
  "LEFT JOIN LATERAL (" ++
  "SELECT eqns.nspname AS operator_schema, eqop.oprname AS operator_name, " ++
  "eqop.oprleft AS left_type, eqop.oprright AS right_type " ++
  "FROM pg_catalog.pg_amop AS eqamop " ++
  "JOIN pg_catalog.pg_operator AS eqop ON eqop.oid = eqamop.amopopr " ++
  "JOIN pg_catalog.pg_namespace AS eqns ON eqns.oid = eqop.oprnamespace " ++
  "WHERE eqamop.amopfamily = opc.opcfamily " ++
  "AND eqamop.amoplefttype = opc.opcintype " ++
  "AND eqamop.amoprighttype = opc.opcintype " ++
  "AND eqamop.amoppurpose = 's' " ++
  "AND ((iam.amname = 'btree' AND eqamop.amopstrategy = 3) " ++
  "OR (iam.amname = 'hash' AND eqamop.amopstrategy = 1)) " ++
  "ORDER BY eqop.oid LIMIT 1) AS eq ON true " ++
  "ORDER BY i.indexrelid, item.ordinality"

end Internal

open Internal

private structure LiveIndex where
  oid : UInt32
  key : Pgx.IndexKey
  ir : Pgx.IndexIR
  deriving Inhabited

private def loadRelationalIndexes (conn : Pg.Connection)
    (relations : Array LiveRelation) (types : Array LiveType) :
    Async (Except Error (Array LiveIndex)) := do
  match ← queryOne conn "read relational pg_index" relationalIndexCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut indexes : Array LiveIndex := #[]
    for row in rows.rows do
      let parsed : Except Error LiveIndex := do
        let oid ← parseUInt32 "read relational pg_index" (← cell "read relational pg_index" row 0)
        let relation : Pgx.RelationKey := {
          schema := ← cell "read relational pg_index" row 1
          name := ← cell "read relational pg_index" row 2
        }
        let indexSchema ← cell "read relational pg_index" row 3
        let name ← cell "read relational pg_index" row 4
        unless indexSchema == relation.schema do
          throw (drift s!"index {indexSchema}.{name} is not in relation schema {relation.schema}")
        let nullsNotDistinct ← parseBool "read relational pg_index"
          (← cell "read relational pg_index" row 12)
        pure {
          oid
          key := { schema := indexSchema, name }
          ir := {
            relation, name
            unique := ← parseBool "read relational pg_index"
              (← cell "read relational pg_index" row 5)
            primary := ← parseBool "read relational pg_index"
              (← cell "read relational pg_index" row 6)
            exclusion := ← parseBool "read relational pg_index"
              (← cell "read relational pg_index" row 7)
            immediate := ← parseBool "read relational pg_index"
              (← cell "read relational pg_index" row 8)
            valid := ← parseBool "read relational pg_index"
              (← cell "read relational pg_index" row 9)
            ready := ← parseBool "read relational pg_index"
              (← cell "read relational pg_index" row 10)
            live := ← parseBool "read relational pg_index"
              (← cell "read relational pg_index" row 11)
            uniqueNullPolicy := if nullsNotDistinct then .notDistinct else .distinct
            accessMethod := some (← cell "read relational pg_index" row 13)
            predicate := ← cell? "read relational pg_index" row 14
            expression := ← cell? "read relational pg_index" row 15
          }
        }
      match parsed with
      | .error error => return .error error
      | .ok value =>
        if relations.any (fun relation => relation.key == value.ir.relation) then
          indexes := indexes.push value
    match ← queryOne conn "read relational index elements" relationalIndexElementSql with
    | .error error => pure (.error error)
    | .ok elementRows =>
      for row in elementRows.rows do
        let parsed : Except Error
            (UInt32 × Nat × Bool × Option String × Option String ×
              Option Pgx.CollationKey × Option Pgx.QualifiedName × Pgx.IndexOrder ×
              Pgx.IndexNullsOrder × Option Pgx.OperatorKey) := do
          let context := "read relational index elements"
          let oid ← parseUInt32 context (← cell context row 0)
          let ordinal ← parseNat context (← cell context row 1)
          let keyElement ← parseBool context (← cell context row 2)
          let column ← cell? context row 3
          let expression ← cell? context row 4
          let collationSchema ← cell? context row 5
          let collationName ← cell? context row 6
          let collation ← match collationSchema, collationName with
            | none, none => pure none
            | some schema, some name => pure (some { schema, name })
            | _, _ => throw (drift s!"{context}: incomplete collation identity")
          let opclassSchema ← cell? context row 7
          let opclassName ← cell? context row 8
          let opclass ← match opclassSchema, opclassName with
            | none, none => pure none
            | some schema, some name => pure (some { schema, name })
            | _, _ => throw (drift s!"{context}: incomplete operator-class identity")
          let descending ← parseBool context (← cell context row 9)
          let nullsFirst ← parseBool context (← cell context row 10)
          let operatorSchema ← cell? context row 11
          let operatorName ← cell? context row 12
          let leftOid ← match ← cell? context row 13 with
            | none => pure none
            | some value => some <$> parseUInt32 context value
          let rightOid ← match ← cell? context row 14 with
            | none => pure none
            | some value => some <$> parseUInt32 context value
          let equalityOperator ← match operatorSchema, operatorName, leftOid, rightOid with
            | none, none, none, none => pure none
            | some schema, some name, some leftOid, some rightOid =>
                some <$> operatorKeyByOperandOids types context schema name leftOid rightOid
            | _, _, _, _ => throw (drift s!"{context}: incomplete equality-operator identity")
          pure (oid, ordinal, keyElement, column, expression, collation, opclass,
            if descending then .descending else .ascending,
            if nullsFirst then .first else .last, equalityOperator)
        match parsed with
        | .error error => return .error error
        | .ok (oid, ordinal, keyElement, column, expression, collation, opclass,
            order, nullsOrder, equalityOperator) =>
          match indexes.findIdx? (fun value => value.oid == oid) with
          | none => pure ()
          | some index =>
            let value := indexes[index]!
            if keyElement then
              let expectedOrdinal := value.ir.keyElements.size + 1
              unless ordinal == expectedOrdinal do
                return .error (drift s!"index {value.key}: expected key ordinal \
                  {expectedOrdinal}, received {ordinal}")
              unless column.isSome != expression.isSome do
                return .error (drift s!"index {value.key}: key must be exactly one column or expression")
              let element : Pgx.IndexKeyElementIR := {
                ordinal, column, expression, collation, opclass, equalityOperator,
                order, nullsOrder
              }
              indexes := indexes.set! index { value with ir := {
                value.ir with
                columns := match column with
                  | some name => value.ir.columns.push name
                  | none => value.ir.columns
                keyElements := value.ir.keyElements.push element
              } }
            else
              let expectedOrdinal := value.ir.keyElements.size +
                value.ir.includedColumns.size + 1
              unless ordinal == expectedOrdinal do
                return .error (drift s!"index {value.key}: expected INCLUDE ordinal \
                  {expectedOrdinal}, received {ordinal}")
              let some name := column
                | return .error (drift s!"index {value.key}: INCLUDE element is not a column")
              if expression.isSome then
                return .error (drift s!"index {value.key}: INCLUDE column has an expression")
              indexes := indexes.set! index { value with ir := {
                value.ir with includedColumns := value.ir.includedColumns.push name
              } }
      pure (.ok indexes)

private def relationalConstraintTypeList (serverMajor : Nat) : String :=
  if serverMajor >= 18 then "'c', 'n', 'p', 'u', 'f', 'x'"
  else "'c', 'p', 'u', 'f', 'x'"

namespace Internal

/-- Versioned relation-constraint query.  PostgreSQL 17 has neither native
NOT NULL constraint rows nor the `conenforced`/`conperiod` columns, so those
values are supplied as semantic literals without mentioning absent columns.
-/
def relationalConstraintCatalogSql (serverMajor : Nat) : String :=
  let enforced := if serverMajor >= 18 then "con.conenforced::text" else "true::text"
  let period := if serverMajor >= 18 then "con.conperiod::text" else "false::text"
  "SELECT con.oid::text, ns.nspname, c.relname, con.conname, con.contype::text, " ++
  "rns.nspname, rc.relname, " ++
  "CASE WHEN con.contype IN ('c', 'x') " ++
  "THEN pg_catalog.pg_get_constraintdef(con.oid, true) ELSE NULL END, " ++
  "con.convalidated::text, " ++ enforced ++ ", con.condeferrable::text, " ++
  "con.condeferred::text, pns.nspname, pc.relname, parent.conname, " ++
  "con.conislocal::text, con.coninhcount::text, con.connoinherit::text, " ++
  period ++ ", ins.nspname, ic.relname, " ++
  "CASE WHEN con.contype = 'f' THEN con.confmatchtype::text END, " ++
  "CASE WHEN con.contype = 'f' THEN con.confupdtype::text END, " ++
  "CASE WHEN con.contype = 'f' THEN con.confdeltype::text END, " ++
  "COALESCE(i.indnullsnotdistinct, false)::text " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "JOIN pg_catalog.pg_class AS c ON c.oid = con.conrelid " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_class AS rc ON rc.oid = NULLIF(con.confrelid, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS rns ON rns.oid = rc.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_constraint AS parent ON parent.oid = NULLIF(con.conparentid, 0) " ++
  "LEFT JOIN pg_catalog.pg_class AS pc ON pc.oid = parent.conrelid " ++
  "LEFT JOIN pg_catalog.pg_namespace AS pns ON pns.oid = pc.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_class AS ic ON ic.oid = NULLIF(con.conindid, 0) " ++
  "LEFT JOIN pg_catalog.pg_namespace AS ins ON ins.oid = ic.relnamespace " ++
  "LEFT JOIN pg_catalog.pg_index AS i ON i.indexrelid = con.conindid " ++
  "WHERE con.conrelid <> 0 AND con.contype IN (" ++
  relationalConstraintTypeList serverMajor ++ ") ORDER BY con.oid"

def relationalConstraintColumnSql (serverMajor : Nat) : String :=
  "SELECT con.oid, false::text, item.ordinality, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.conkey) " ++
  "WITH ORDINALITY AS item(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.conrelid AND a.attnum = item.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype IN (" ++
  relationalConstraintTypeList serverMajor ++ ") UNION ALL " ++
  "SELECT con.oid, true::text, item.ordinality, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.confkey) " ++
  "WITH ORDINALITY AS item(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.confrelid AND a.attnum = item.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype = 'f' ORDER BY 1, 2, 3"

def relationalConstraintDeleteSetColumnSql : String :=
  "SELECT con.oid::text, item.ordinality::text, a.attname " ++
  "FROM pg_catalog.pg_constraint AS con " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(con.confdelsetcols) " ++
  "WITH ORDINALITY AS item(attnum, ordinality) " ++
  "JOIN pg_catalog.pg_attribute AS a " ++
  "ON a.attrelid = con.conrelid AND a.attnum = item.attnum " ++
  "WHERE con.conrelid <> 0 AND con.contype = 'f' " ++
  "ORDER BY con.oid, item.ordinality"

def relationalConstraintOperatorSql : String :=
  let branch (field tag : String) :=
    "SELECT con.oid, '" ++ tag ++ "'::text, item.ordinality, " ++
    "ons.nspname, op.oprname, op.oprleft::text, op.oprright::text " ++
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

end Internal

private structure LiveConstraint where
  oid : UInt32
  ir : Pgx.ConstraintIR
  localColumnOrdinal : Nat := 0
  referencedColumnOrdinal : Nat := 0
  exclusionOperators : Array Pgx.OperatorKey := #[]
  deriving Inhabited

private structure RelationNotNull where
  relation : Pgx.RelationKey
  column : String
  deriving BEq

private def canonicalNotNull (value : RelationNotNull)
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

private def nativeNotNullKey (constraint : Pgx.ConstraintIR) :
    Except Error RelationNotNull := do
  unless constraint.columns.size == 1 do
    throw (drift s!"native NOT NULL constraint {constraint.relation}.{constraint.name} \
      must name exactly one column")
  if constraint.referencedRelation.isSome || !constraint.referencedColumns.isEmpty ||
      constraint.expression.isSome || constraint.localExpression.isSome ||
      constraint.deferrable || constraint.initiallyDeferred || constraint.period ||
      constraint.supportingIndex.isSome ||
      !constraint.foreignKeyDeleteSetColumns.isEmpty ||
      !constraint.referencedToReferencingOperators.isEmpty ||
      !constraint.referencedEqualityOperators.isEmpty ||
      !constraint.referencingEqualityOperators.isEmpty ||
      !constraint.exclusionElements.isEmpty then
    throw (drift s!"native NOT NULL constraint {constraint.relation}.{constraint.name} \
      has unexpected catalog metadata")
  pure { relation := constraint.relation, column := constraint.columns[0]! }

namespace Internal

/-- PostgreSQL 18 may set `pg_attribute.attnotnull` for an enforced but
unvalidated native NOT NULL constraint while pre-existing NULL values remain.
Until relation nullability is derived from lifecycle-aware metadata, such a
column cannot safely back a generated non-optional decoder. -/
def validateNotNullReadSafety (serverMajor : Nat)
    (constraints : Array Pgx.ConstraintIR) : Except Error Unit := do
  if serverMajor < 18 then return
  for constraint in constraints do
    if constraint.kind == .notNull && (!constraint.validated || !constraint.enforced) then
      throw (drift s!"cannot trust relation nullability for native NOT NULL \
        constraint {constraint.relation}.{constraint.name}: enforced={constraint.enforced}, \
        validated={constraint.validated}")

end Internal

private def normalizeNotNullConstraints (serverMajor : Nat)
    (catalog : Array Pgx.ConstraintIR) (relations : Array LiveRelation) :
    Except Error (Array Pgx.ConstraintIR) := do
  validateNotNullReadSafety serverMajor catalog
  let mut attributes : Array RelationNotNull := #[]
  for relation in relations do
    for column in relation.columns do
      if column.attributeNotNull then
        attributes := attributes.push { relation := relation.key, column := column.name }
  let mut result : Array Pgx.ConstraintIR := #[]
  let mut nativeKeys : Array RelationNotNull := #[]
  for constraint in catalog do
    if constraint.kind == .notNull then
      unless serverMajor >= 18 do
        throw (drift s!"PostgreSQL {serverMajor} returned a native NOT NULL constraint")
      let key ← nativeNotNullKey constraint
      unless attributes.contains key do
        throw (drift s!"native NOT NULL constraint for {key.relation}.{key.column} \
          is absent from pg_attribute")
      if nativeKeys.contains key then
        throw (drift s!"duplicate native NOT NULL constraint for {key.relation}.{key.column}")
      nativeKeys := nativeKeys.push key
      let normalized := canonicalNotNull key (some constraint)
      if result.any (fun existing => existing.key == normalized.key) then
        throw (drift s!"duplicate normalized constraint identity {normalized.key}")
      result := result.push normalized
    else
      if result.any (fun existing => existing.key == constraint.key) then
        throw (drift s!"duplicate normalized constraint identity {constraint.key}")
      result := result.push constraint
  for key in attributes do
    unless nativeKeys.contains key do
      let normalized := canonicalNotNull key
      if result.any (fun existing => existing.key == normalized.key) then
        throw (drift s!"synthetic NOT NULL identity {normalized.key} collides \
          with a PostgreSQL constraint name")
      result := result.push normalized
  pure result

private def loadRelationalConstraints (conn : Pg.Connection) (serverMajor : Nat)
    (relations : Array LiveRelation) (types : Array LiveType)
    (indexes : Array LiveIndex) :
    Async (Except Error (Array Pgx.ConstraintIR)) := do
  match ← queryOne conn "read relational pg_constraint"
      (relationalConstraintCatalogSql serverMajor) with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut constraints : Array LiveConstraint := #[]
    for row in rows.rows do
      let parsed : Except Error LiveConstraint := do
        let context := "read relational pg_constraint"
        let oid ← parseUInt32 context (← cell context row 0)
        let relation : Pgx.RelationKey := {
          schema := ← cell context row 1
          name := ← cell context row 2
        }
        let name ← cell context row 3
        let kind ← parseConstraintKind context (← cell context row 4)
        if kind == .notNull && serverMajor < 18 then
          throw (drift s!"PostgreSQL {serverMajor} returned a native NOT NULL constraint")
        let referencedSchema ← cell? context row 5
        let referencedName ← cell? context row 6
        let referencedRelation ← match referencedSchema, referencedName with
          | none, none => pure none
          | some schema, some name => pure (some { schema, name })
          | _, _ => throw (drift s!"{context}: incomplete referenced relation identity")
        let expression ← cell? context row 7
        let validated ← parseBool context (← cell context row 8)
        let enforced ← parseBool context (← cell context row 9)
        let deferrable ← parseBool context (← cell context row 10)
        let initiallyDeferred ← parseBool context (← cell context row 11)
        if initiallyDeferred && !deferrable then
          throw (drift s!"constraint {relation}.{name} is initially deferred but not deferrable")
        let parentSchema ← cell? context row 12
        let parentRelationName ← cell? context row 13
        let parentName ← cell? context row 14
        let parent ← match parentSchema, parentRelationName, parentName with
          | none, none, none => pure none
          | some schema, some relationName, some name => pure (some {
              relation := { schema, name := relationName }, name
            })
          | _, _, _ => throw (drift s!"{context}: incomplete parent constraint identity")
        let isLocal ← parseBool context (← cell context row 15)
        let inheritanceCount ← parseNat context (← cell context row 16)
        let noInherit ← parseBool context (← cell context row 17)
        let period ← parseBool context (← cell context row 18)
        let indexSchema ← cell? context row 19
        let indexName ← cell? context row 20
        let supportingIndex ← match indexSchema, indexName with
          | none, none => pure none
          | some schema, some name => pure (some { schema, name })
          | _, _ => throw (drift s!"{context}: incomplete supporting index identity")
        let foreignKeyMatch ← match ← cell? context row 21 with
          | some value => parseForeignKeyMatch context value
          | none => do
            if kind == .foreignKey then
              throw (drift s!"foreign key {relation}.{name} has no match type")
            else pure .simple
        let foreignKeyOnUpdate ← match ← cell? context row 22 with
          | some value => parseForeignKeyAction context value
          | none => do
            if kind == .foreignKey then
              throw (drift s!"foreign key {relation}.{name} has no update action")
            else pure .noAction
        let foreignKeyOnDelete ← match ← cell? context row 23 with
          | some value => parseForeignKeyAction context value
          | none => do
            if kind == .foreignKey then
              throw (drift s!"foreign key {relation}.{name} has no delete action")
            else pure .noAction
        let nullsNotDistinct ← parseBool context (← cell context row 24)
        pure { oid, ir := {
          relation, name, kind, referencedRelation, expression,
          enforced, validated, deferrable, initiallyDeferred, parent, isLocal,
          inheritanceCount, noInherit, period, supportingIndex,
          uniqueNullPolicy := if nullsNotDistinct then .notDistinct else .distinct,
          foreignKeyMatch, foreignKeyOnUpdate, foreignKeyOnDelete
        } }
      match parsed with
      | .error error => return .error error
      | .ok value =>
        if relations.any (fun relation => relation.key == value.ir.relation) then
          constraints := constraints.push value
    match ← queryOne conn "read relational constraint columns"
        (relationalConstraintColumnSql serverMajor) with
    | .error error => pure (.error error)
    | .ok columnRows =>
      for row in columnRows.rows do
        let parsed : Except Error (UInt32 × Bool × Nat × String) := do
          let context := "read relational constraint columns"
          pure (← parseUInt32 context (← cell context row 0),
            ← parseBool context (← cell context row 1),
            ← parseNat context (← cell context row 2), ← cell context row 3)
        match parsed with
        | .error error => return .error error
        | .ok (oid, referenced, ordinal, name) =>
          match constraints.findIdx? (fun value => value.oid == oid) with
          | none => pure ()
          | some index =>
            let value := constraints[index]!
            let expectedOrdinal := if referenced then value.ir.referencedColumns.size + 1
              else value.ir.columns.size + 1
            let lastOrdinal := if referenced then value.referencedColumnOrdinal
              else value.localColumnOrdinal
            let ordinalValid := if !referenced && value.ir.kind == .exclusion then
                ordinal > lastOrdinal
              else
                ordinal == expectedOrdinal
            unless ordinalValid do
              return .error (drift s!"constraint {value.ir.relation}.{value.ir.name}: \
                invalid column ordinal {ordinal} after {lastOrdinal}")
            let ir := if referenced then { value.ir with
                referencedColumns := value.ir.referencedColumns.push name }
              else { value.ir with columns := value.ir.columns.push name }
            let value := if referenced then
                { value with ir, referencedColumnOrdinal := ordinal }
              else
                { value with ir, localColumnOrdinal := ordinal }
            constraints := constraints.set! index value
      match ← queryOne conn "read foreign-key delete-set columns"
          relationalConstraintDeleteSetColumnSql with
      | .error error => pure (.error error)
      | .ok deleteRows =>
        for row in deleteRows.rows do
          let parsed : Except Error (UInt32 × Nat × String) := do
            let context := "read foreign-key delete-set columns"
            pure (← parseUInt32 context (← cell context row 0),
              ← parseNat context (← cell context row 1), ← cell context row 2)
          match parsed with
          | .error error => return .error error
          | .ok (oid, ordinal, name) =>
            match constraints.findIdx? (fun value => value.oid == oid) with
            | none => pure ()
            | some index =>
              let value := constraints[index]!
              let expectedOrdinal := value.ir.foreignKeyDeleteSetColumns.size + 1
              unless ordinal == expectedOrdinal do
                return .error (drift s!"foreign key {value.ir.relation}.{value.ir.name}: \
                  expected delete-set ordinal {expectedOrdinal}, received {ordinal}")
              constraints := constraints.set! index { value with ir := {
                value.ir with foreignKeyDeleteSetColumns :=
                  value.ir.foreignKeyDeleteSetColumns.push name
              } }
        match ← queryOne conn "read relational constraint operators"
            relationalConstraintOperatorSql with
        | .error error => pure (.error error)
        | .ok operatorRows =>
          for row in operatorRows.rows do
            let parsed : Except Error (UInt32 × String × Nat × Pgx.OperatorKey) := do
              let context := "read relational constraint operators"
              let oid ← parseUInt32 context (← cell context row 0)
              let vector ← cell context row 1
              let ordinal ← parseNat context (← cell context row 2)
              let schema ← cell context row 3
              let name ← cell context row 4
              let leftOid ← parseUInt32 context (← cell context row 5)
              let rightOid ← parseUInt32 context (← cell context row 6)
              pure (oid, vector, ordinal, ← operatorKeyByOperandOids types context
                schema name leftOid rightOid)
            match parsed with
            | .error error => return .error error
            | .ok (oid, vector, ordinal, key) =>
              match constraints.findIdx? (fun value => value.oid == oid) with
              | none => pure ()
              | some index =>
                let value := constraints[index]!
                let current? := match vector with
                  | "pf" => some value.ir.referencedToReferencingOperators
                  | "pp" => some value.ir.referencedEqualityOperators
                  | "ff" => some value.ir.referencingEqualityOperators
                  | "exclude" => some value.exclusionOperators
                  | _ => none
                let some current := current?
                  | return .error (drift s!"constraint {value.ir.relation}.{value.ir.name}: \
                      unknown operator vector {vector}")
                unless ordinal == current.size + 1 do
                  return .error (drift s!"constraint {value.ir.relation}.{value.ir.name}: \
                    expected {vector} operator ordinal {current.size + 1}, received {ordinal}")
                let updated := match vector with
                  | "pf" => { value with ir := { value.ir with
                      referencedToReferencingOperators := current.push key } }
                  | "pp" => { value with ir := { value.ir with
                      referencedEqualityOperators := current.push key } }
                  | "ff" => { value with ir := { value.ir with
                      referencingEqualityOperators := current.push key } }
                  | "exclude" => { value with exclusionOperators := current.push key }
                  | _ => value
                constraints := constraints.set! index updated
          for index in [:constraints.size] do
            let value := constraints[index]!
            let checked : Except Error Pgx.ConstraintIR := match value.ir.kind with
              | .primaryKey | .unique => do
                let some key := value.ir.supportingIndex
                  | throw (drift s!"constraint {value.ir.relation}.{value.ir.name} has no supporting index")
                let some supporting := indexes.find? (fun index => index.key == key)
                  | throw (drift s!"constraint {value.ir.relation}.{value.ir.name} refers to missing index {key}")
                unless supporting.ir.relation == value.ir.relation do
                  throw (drift s!"constraint {value.ir.relation}.{value.ir.name} is backed by index {key} on {supporting.ir.relation}")
                unless supporting.ir.uniqueNullPolicy == value.ir.uniqueNullPolicy do
                  throw (drift s!"constraint {value.ir.relation}.{value.ir.name} disagrees with index {key} on null uniqueness")
                unless supporting.ir.keyElements.size == value.ir.columns.size do
                  throw (drift s!"constraint {value.ir.relation}.{value.ir.name} has unaligned key columns")
                pure value.ir
              | .foreignKey => do
                unless value.ir.referencedRelation.isSome do
                  throw (drift s!"foreign key {value.ir.relation}.{value.ir.name} has no referenced relation")
                let width := value.ir.columns.size
                unless width > 0 && value.ir.referencedColumns.size == width do
                  throw (drift s!"foreign key {value.ir.relation}.{value.ir.name} has unaligned key columns")
                unless value.ir.referencedToReferencingOperators.size == width &&
                    value.ir.referencedEqualityOperators.size == width &&
                    value.ir.referencingEqualityOperators.size == width do
                  throw (drift s!"foreign key {value.ir.relation}.{value.ir.name} has unaligned equality-operator vectors")
                for name in value.ir.foreignKeyDeleteSetColumns do
                  unless value.ir.columns.contains name do
                    throw (drift s!"foreign key {value.ir.relation}.{value.ir.name} has unknown delete-set column {name}")
                let some key := value.ir.supportingIndex
                  | throw (drift s!"foreign key {value.ir.relation}.{value.ir.name} has no referenced index")
                unless indexes.any (fun index => index.key == key) do
                  throw (drift s!"foreign key {value.ir.relation}.{value.ir.name} refers to missing index {key}")
                pure value.ir
              | .exclusion => do
                let some key := value.ir.supportingIndex
                  | throw (drift s!"exclusion constraint {value.ir.relation}.{value.ir.name} has no supporting index")
                let some supporting := indexes.find? (fun index => index.key == key)
                  | throw (drift s!"exclusion constraint {value.ir.relation}.{value.ir.name} refers to missing index {key}")
                unless supporting.ir.relation == value.ir.relation do
                  throw (drift s!"exclusion constraint {value.ir.relation}.{value.ir.name} is backed by index {key} on {supporting.ir.relation}")
                unless supporting.ir.keyElements.size == value.exclusionOperators.size do
                  throw (drift s!"exclusion constraint {value.ir.relation}.{value.ir.name} has unaligned operators")
                let mut elements : Array Pgx.ExclusionElementIR := #[]
                for ordinal in [:supporting.ir.keyElements.size] do
                  elements := elements.push {
                    key := supporting.ir.keyElements[ordinal]!
                    operator := value.exclusionOperators[ordinal]!
                  }
                pure { value.ir with exclusionElements := elements }
              | .check | .notNull => do
                if value.ir.supportingIndex.isSome then
                  throw (drift s!"constraint {value.ir.relation}.{value.ir.name} unexpectedly has a supporting index")
                pure value.ir
            match checked with
            | .error error => return .error error
            | .ok ir => constraints := constraints.set! index { value with ir }
          pure (normalizeNotNullConstraints serverMajor
            (constraints.map (fun value => value.ir)) relations)

private def viewCatalogSql : String :=
  "SELECT c.oid::text, ns.nspname, c.relname, c.relkind::text, " ++
  "pg_catalog.pg_get_viewdef(c.oid, true), " ++
  "COALESCE((SELECT option_value FROM pg_catalog.pg_options_to_table(c.reloptions) " ++
  "WHERE option_name = 'check_option'), 'none'), " ++
  "COALESCE((SELECT option_value FROM pg_catalog.pg_options_to_table(c.reloptions) " ++
  "WHERE option_name = 'security_barrier'), 'false'), " ++
  "COALESCE((SELECT option_value FROM pg_catalog.pg_options_to_table(c.reloptions) " ++
  "WHERE option_name = 'security_invoker'), 'false') " ++
  "FROM pg_catalog.pg_class AS c " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = c.relnamespace " ++
  "WHERE c.relkind IN ('v', 'm') " ++
  "AND NOT EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
  "WHERE dep.classid = 'pg_catalog.pg_class'::pg_catalog.regclass " ++
  "AND dep.objid = c.oid " ++
  "AND dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass " ++
  "AND dep.deptype = 'e') " ++
  "ORDER BY ns.nspname, c.relname"

private def loadViews (conn : Pg.Connection) (schemas : Array String) :
    Async (Except Error (Array Pgx.ViewIR)) := do
  match ← queryOne conn "read view metadata" viewCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut views : Array Pgx.ViewIR := #[]
    for row in rows.rows do
      let parsed : Except Error (String × Pgx.ViewIR) := do
        let _ ← parseUInt32 "read view metadata" (← cell "read view metadata" row 0)
        let schema ← cell "read view metadata" row 1
        let name ← cell "read view metadata" row 2
        let kind ← cell "read view metadata" row 3
        unless kind == "v" || kind == "m" do
          throw (drift s!"read view metadata: unknown relation kind {kind}")
        let definition ← cell "read view metadata" row 4
        let rawCheckOption ← cell "read view metadata" row 5
        let rawBarrier ← cell "read view metadata" row 6
        let rawInvoker ← cell "read view metadata" row 7
        let materialized := kind == "m"
        let checkOption ← if materialized then pure .none else
          parseViewCheckOption "read view metadata" rawCheckOption
        let securityBarrier ← if materialized then pure false else
          parseBool "read view metadata" rawBarrier
        let securityInvoker ← if materialized then pure false else
          parseBool "read view metadata" rawInvoker
        pure (schema, {
          relation := { schema, name }
          definition
          checkOption
          securityBarrier
          securityInvoker
        })
      match parsed with
      | .error error => return .error error
      | .ok (schema, view) =>
        if schemas.contains schema then views := views.push view
    pure (.ok views)

private structure LiveRoutine where
  oid : UInt32
  returnTypeOid : UInt32
  inputCount : Nat
  defaultCount : Nat
  ir : Pgx.RoutineIR
  deriving Inhabited

private def routineCatalogSql : String :=
  "SELECT p.oid::text, ns.nspname, p.proname, p.prokind::text, " ++
  "p.proretset::text, p.prorettype::text, p.pronargs::text, " ++
  "p.pronargdefaults::text, p.proisstrict::text, p.provolatile::text, " ++
  "p.proparallel::text, p.prosecdef::text " ++
  "FROM pg_catalog.pg_proc AS p " ++
  "JOIN pg_catalog.pg_namespace AS ns ON ns.oid = p.pronamespace " ++
  "WHERE NOT EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
  "WHERE dep.classid = 'pg_catalog.pg_proc'::pg_catalog.regclass " ++
  "AND dep.objid = p.oid " ++
  "AND dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass " ++
  "AND dep.deptype = 'e') " ++
  "ORDER BY p.oid"

private def routineArgCatalogSql : String :=
  "SELECT p.oid::text, args.ordinality::text, " ++
  "NULLIF(p.proargnames[args.ordinality], ''), " ++
  "COALESCE(p.proargmodes[args.ordinality], 'i')::text, args.type_oid::text " ++
  "FROM pg_catalog.pg_proc AS p " ++
  "CROSS JOIN LATERAL pg_catalog.unnest(" ++
  "COALESCE(p.proallargtypes, p.proargtypes::oid[])) " ++
  "WITH ORDINALITY AS args(type_oid, ordinality) " ++
  "WHERE NOT EXISTS (SELECT 1 FROM pg_catalog.pg_depend AS dep " ++
  "WHERE dep.classid = 'pg_catalog.pg_proc'::pg_catalog.regclass " ++
  "AND dep.objid = p.oid " ++
  "AND dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass " ++
  "AND dep.deptype = 'e') " ++
  "ORDER BY p.oid, args.ordinality"

private def isRoutineOutput : Pgx.RoutineArgMode → Bool
  | .output | .inputOutput | .table => true
  | .input | .variadic => false

private def loadRoutines (conn : Pg.Connection) (schemas : Array String)
    (types : Array LiveType) : Async (Except Error (Array Pgx.RoutineIR)) := do
  let mut routines : Array LiveRoutine := #[]
  match ← queryOne conn "read pg_proc" routineCatalogSql with
  | .error error => return .error error
  | .ok rows =>
    for row in rows.rows do
      let parsed : Except Error LiveRoutine := do
        let oid ← parseUInt32 "read pg_proc" (← cell "read pg_proc" row 0)
        let schema ← cell "read pg_proc" row 1
        let name ← cell "read pg_proc" row 2
        let kind ← parseRoutineKind "read pg_proc" (← cell "read pg_proc" row 3)
        let returnsSet ← parseBool "read pg_proc" (← cell "read pg_proc" row 4)
        let returnTypeOid ← parseUInt32 "read pg_proc" (← cell "read pg_proc" row 5)
        let inputCount ← parseNat "read pg_proc" (← cell "read pg_proc" row 6)
        let defaultCount ← parseNat "read pg_proc" (← cell "read pg_proc" row 7)
        let strict ← parseBool "read pg_proc" (← cell "read pg_proc" row 8)
        let volatility ← cell "read pg_proc" row 9
        let parallel ← cell "read pg_proc" row 10
        let securityDefiner ← parseBool "read pg_proc" (← cell "read pg_proc" row 11)
        pure {
          oid, returnTypeOid, inputCount, defaultCount
          ir := {
            key := { schema, name }
            kind, args := #[], returnsSet
            strict, volatility, parallel, securityDefiner
          }
        }
      match parsed with
      | .error error => return .error error
      | .ok value => routines := routines.push value
  match ← queryOne conn "read pg_proc arguments" routineArgCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    for row in rows.rows do
      let parsed : Except Error (UInt32 × Nat × Pgx.RoutineArgIR) := do
        let oid ← parseUInt32 "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 0)
        let ordinal ← parseNat "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 1)
        let name ← cell? "read pg_proc arguments" row 2
        let mode ← parseRoutineArgMode "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 3)
        let typeOid ← parseUInt32 "read pg_proc arguments"
          (← cell "read pg_proc arguments" row 4)
        pure (oid, ordinal, {
          name, mode
          ty := ← liveTypeRefByOid types "read pg_proc arguments" typeOid
        })
      match parsed with
      | .error error => return .error error
      | .ok (oid, ordinal, arg) =>
        match routines.findIdx? (fun value => value.oid == oid) with
        | none => pure ()
        | some index =>
          let value := routines[index]!
          unless ordinal == value.ir.args.size + 1 do
            return .error (drift s!"routine {value.ir.key.schema}.{value.ir.key.name} \
              has non-dense argument ordinal {ordinal}")
          routines := routines.set! index {
            value with ir := { value.ir with args := value.ir.args.push arg }
          }
    for index in [0:routines.size] do
      let value := routines[index]!
      let inputArgs := value.ir.args.filter (fun arg => arg.mode.isInput)
      unless inputArgs.size == value.inputCount do
        return .error (drift s!"routine {value.ir.key.schema}.{value.ir.key.name} \
          reports {value.inputCount} input arguments but exposes {inputArgs.size}")
      unless value.defaultCount ≤ value.inputCount do
        return .error (drift s!"routine {value.ir.key.schema}.{value.ir.key.name} \
          has more defaults than input arguments")
      let firstDefault := value.inputCount - value.defaultCount
      let mut inputPosition := 0
      let mut outputPosition := 0
      let mut args : Array Pgx.RoutineArgIR := #[]
      let mut results : Array Pgx.RoutineResultColumnIR := #[]
      for arg in value.ir.args do
        let hasDefault := arg.mode.isInput && firstDefault < inputPosition + 1
        if arg.mode.isInput then inputPosition := inputPosition + 1
        let arg := { arg with hasDefault }
        args := args.push arg
        if isRoutineOutput arg.mode then
          outputPosition := outputPosition + 1
          results := results.push {
            name := arg.name.getD s!"column{outputPosition}"
            ordinal := outputPosition
            ty := arg.ty
          }
      let returnTypeResult : Except Error (Option Pgx.TypeRef) :=
        if value.ir.kind == .procedure then pure none else
          some <$> liveTypeRefByOid types
            s!"routine {value.ir.key.schema}.{value.ir.key.name}" value.returnTypeOid
      let returnType ← match returnTypeResult with
        | .ok result => pure result
        | .error error => return .error error
      if schemas.contains value.ir.key.schema && value.ir.returnsSet && results.isEmpty then
        match returnType with
        | some ref =>
          if ref.key.kind == .composite then
            let candidates := types.filter (fun ty => ty.key == ref.key)
            let some composite := candidates[0]?
              | return .error (drift s!"set-returning routine {value.ir.key} \
                  refers to missing composite result {ref.key}")
            unless candidates.size == 1 do
              return .error (drift s!"set-returning routine {value.ir.key} \
                has ambiguous composite result {ref.key}")
            for field in composite.compositeFields do
              results := results.push {
                name := field.name
                ordinal := results.size + 1
                ty := field.ty
              }
        | none => pure ()
      let dynamicRecord := match returnType with
        | some ref => ref.key.kind == .pseudo && ref.key.name == "record" && results.isEmpty
        | none => false
      let ir := {
        value.ir with
          key := { value.ir.key with inputTypes := inputArgs.map (fun arg => arg.ty) }
          args
          returnType
          resultColumns := results
          dynamicRecord
      }
      routines := routines.set! index { value with ir }
    pure (.ok (routines.filter (fun value =>
      schemas.contains value.ir.key.schema) |>.map (fun value => value.ir)))

private def extensionCatalogSql : String :=
  "SELECT extname, extversion FROM pg_catalog.pg_extension ORDER BY extname"

private def loadExtensions (conn : Pg.Connection) :
    Async (Except Error (Array (String × String))) := do
  match ← queryOne conn "read pg_extension" extensionCatalogSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut extensions : Array (String × String) := #[]
    for row in rows.rows do
      let parsed : Except Error (String × String) := do
        pure (← cell "read pg_extension" row 0, ← cell "read pg_extension" row 1)
      match parsed with
      | .error error => return .error error
      | .ok value => extensions := extensions.push value
    pure (.ok extensions)

namespace Internal

/-- Symbolic extension membership recovered from live `pg_depend` rows. -/
structure ExtensionTypeOwnership where
  key : Pgx.TypeKey
  extension : String
  deriving Repr, BEq, Inhabited

/-- Query proving that a type is an extension member rather than merely
sharing an extension's schema or name. -/
def extensionTypeOwnershipSql : String :=
  "SELECT dep.objid::text, ext.extname " ++
  "FROM pg_catalog.pg_depend AS dep " ++
  "JOIN pg_catalog.pg_extension AS ext ON ext.oid = dep.refobjid " ++
  "WHERE dep.classid = 'pg_catalog.pg_type'::pg_catalog.regclass " ++
  "AND dep.objsubid = 0 " ++
  "AND dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass " ++
  "AND dep.refobjsubid = 0 " ++
  "AND dep.deptype = 'e' " ++
  "ORDER BY dep.objid, ext.extname"

end Internal

private def loadExtensionTypeOwnership (conn : Pg.Connection)
    (types : Array LiveType) :
    Async (Except Error (Array ExtensionTypeOwnership)) := do
  match ← queryOne conn "read extension type ownership" extensionTypeOwnershipSql with
  | .error error => pure (.error error)
  | .ok rows =>
    let mut ownership : Array ExtensionTypeOwnership := #[]
    for row in rows.rows do
      let parsed : Except Error ExtensionTypeOwnership := do
        let oid ← parseUInt32 "read extension type ownership"
          (← cell "read extension type ownership" row 0)
        let candidates := types.filter (fun value => value.oid == oid)
        let some ty := candidates[0]?
          | throw (drift s!"extension dependency refers to missing type OID {oid}")
        unless candidates.size == 1 do
          throw (drift s!"extension dependency has ambiguous type OID {oid}")
        pure { key := ty.key, extension := ← cell "read extension type ownership" row 1 }
      match parsed with
      | .error error => return .error error
      | .ok value => ownership := ownership.push value
    pure (.ok ownership)

private def metadataSchemas (db : DatabaseDesc) : Array String := Id.run do
  let mut schemas : Array String := #[]
  for relation in db.relations do
    unless schemas.contains relation.key.schema do
      schemas := schemas.push relation.key.schema
  for view in db.views do
    unless schemas.contains view.relation.schema do
      schemas := schemas.push view.relation.schema
  for routine in db.routines do
    unless schemas.contains routine.key.schema do
      schemas := schemas.push routine.key.schema
  return schemas

private def sortedStrings (values : Array String) : Array String :=
  values.toList.mergeSort (fun left right => compare left right == .lt) |>.toArray

private def catalogConstraintView (value : Pgx.ConstraintIR) : Pgx.ConstraintIR :=
  { value with
    -- The typed local expression is a code-generation derivation of the
    -- normalized catalog definition, not an independent live-catalog field.
    localExpression := none
    foreignKeyDeleteSetColumns := sortedStrings value.foreignKeyDeleteSetColumns
  }

namespace Internal

/-- Compare relation constraints as an unordered, duplicate-free collection.
Ordered column/operator vectors remain ordered; only the documented set-like
foreign-key delete subset is canonicalized. -/
def validateConstraintMetadata (expected actual : Array Pgx.ConstraintIR) :
    Except Error Unit := do
  unless actual.size == expected.size do
    throw (drift s!"constraint metadata count drift: expected {expected.size}, received {actual.size}")
  let mut seen : Array Pgx.ConstraintKey := #[]
  for want in expected do
    let key := want.key
    if seen.contains key then
      throw (drift s!"generated constraint metadata duplicates {key}")
    seen := seen.push key
    let candidates := actual.filter (fun value => value.key == key)
    let some found := candidates[0]?
      | throw (drift s!"required constraint metadata is missing: {key}")
    unless candidates.size == 1 do
      throw (drift s!"constraint metadata identity is ambiguous: {key}")
    let want := catalogConstraintView want
    let found := catalogConstraintView found
    unless found == want do
      throw (drift s!"constraint metadata drift for {key}: expected \
        {repr want}, received {repr found}")

private def isSemanticIndex (value : Pgx.IndexIR) : Bool :=
  value.unique || value.primary || value.exclusion

private def catalogIndexView (value : Pgx.IndexIR) : Pgx.IndexIR :=
  { value with includedColumns := sortedStrings value.includedColumns }

/-- Compare indexes that carry relational meaning.  Plain non-unique indexes
are intentionally ignored: they are performance objects and do not justify a
generated integrity proposition. -/
def validateIndexMetadata (expected actual : Array Pgx.IndexIR) : Except Error Unit := do
  let expected := expected.filter isSemanticIndex
  let actual := actual.filter isSemanticIndex
  unless actual.size == expected.size do
    throw (drift s!"relational index metadata count drift: expected {expected.size}, received {actual.size}")
  let mut seen : Array Pgx.IndexKey := #[]
  for want in expected do
    let key := want.key
    if seen.contains key then
      throw (drift s!"generated relational index metadata duplicates {key}")
    seen := seen.push key
    let candidates := actual.filter (fun value => value.key == key)
    let some found := candidates[0]?
      | throw (drift s!"required relational index metadata is missing: {key}")
    unless candidates.size == 1 do
      throw (drift s!"relational index metadata identity is ambiguous: {key}")
    let want := catalogIndexView want
    let found := catalogIndexView found
    unless found == want do
      throw (drift s!"relational index metadata drift for {key}: expected \
        {repr want}, received {repr found}")

/-- Compare live semantic view metadata as an unordered, duplicate-free set. -/
def validateViewMetadata (expected actual : Array Pgx.ViewIR) : Except Error Unit := do
  unless actual.size == expected.size do
    throw (drift s!"view metadata count drift: expected {expected.size}, received {actual.size}")
  for want in expected do
    let candidates := actual.filter (fun value => value.relation == want.relation)
    let some found := candidates[0]?
      | throw (drift s!"required view metadata is missing: {want.relation}")
    unless candidates.size == 1 do
      throw (drift s!"view metadata identity is ambiguous: {want.relation}")
    unless found == want do
      throw (drift s!"view metadata drift for {want.relation}: expected \
        {repr want}, received {repr found}")

/-- Compare live routine metadata by PostgreSQL overload identity. -/
def validateRoutineMetadata (expected actual : Array Pgx.RoutineIR) : Except Error Unit := do
  unless actual.size == expected.size do
    throw (drift s!"routine metadata count drift: expected {expected.size}, received {actual.size}")
  for want in expected do
    let candidates := actual.filter (fun value => value.key == want.key)
    let some found := candidates[0]?
      | throw (drift s!"required routine metadata is missing: {want.key}")
    unless candidates.size == 1 do
      throw (drift s!"routine metadata identity is ambiguous: {want.key}")
    unless found == want do
      throw (drift s!"routine metadata drift for {want.key}: expected \
        {repr want}, received {repr found}")

/-- Validate installed versions and the internal provenance of generated
extension codec packages.  Installed extensions outside the required set do
not affect the contract. -/
def validateExtensionMetadata (db : DatabaseDesc)
    (installed : Array (String × String))
    (ownership : Array ExtensionTypeOwnership) : Except Error Unit := do
  let mut requiredNames : Array String := #[]
  for required in db.requiredExtensions do
    if requiredNames.contains required.1 then
      throw (drift s!"required extension metadata duplicates {required.1}")
    requiredNames := requiredNames.push required.1
    let candidates := installed.filter (fun value => value.1 == required.1)
    let some found := candidates[0]?
      | throw (drift s!"required extension {required.1} is not installed")
    unless candidates.size == 1 do
      throw (drift s!"installed extension identity is ambiguous: {required.1}")
    unless found.2 == required.2 do
      throw (drift s!"extension version drift for {required.1}: expected \
        {required.2}, received {found.2}")
  let mut packageExtensions : Array String := #[]
  let mut packageTypes : Array Pgx.TypeKey := #[]
  for package in db.extensionCodecPackages do
    if packageExtensions.contains package.extension then
      throw (drift s!"extension codec package metadata duplicates {package.extension}")
    packageExtensions := packageExtensions.push package.extension
    let candidates := db.requiredExtensions.filter (fun value => value.1 == package.extension)
    let some required := candidates[0]?
      | throw (drift s!"extension codec package {package.extension} is not required")
    unless candidates.size == 1 && package.version == required.2 do
      throw (drift s!"extension codec package provenance drift for {package.extension}")
    if package.importModule.isEmpty then
      throw (drift s!"extension codec package {package.extension} has no import module")
    if package.types.isEmpty then
      throw (drift s!"extension codec package {package.extension} has no type keys")
    for key in package.types do
      if packageTypes.contains key then
        throw (drift s!"extension codec package type metadata duplicates {key}")
      packageTypes := packageTypes.push key
      unless db.types.any (fun value => value.key == key) do
        throw (drift s!"extension codec package {package.extension} refers to missing type {key}")
      let owners := ownership.filter (fun value => value.key == key)
      let some owner := owners[0]?
        | throw (drift s!"extension codec package type {key} is not an extension member")
      unless owners.size == 1 do
        throw (drift s!"extension codec package type {key} has ambiguous extension ownership")
      unless owner.extension == package.extension do
        throw (drift s!"extension codec package type {key} belongs to \
          {owner.extension}, not {package.extension}")

end Internal

private def checkTypes (db : DatabaseDesc) (live : Array LiveType) :
    Except Error (Array ResolvedType) := do
  let mut resolved : Array ResolvedType := #[]
  for expected in db.types do
    let foundMatches := live.filter (fun value => value.key == expected.key)
    let some actual := foundMatches[0]?
      | throw (drift s!"required PostgreSQL type is missing: {expected.key}")
    if foundMatches.size != 1 then
      throw (drift s!"PostgreSQL type identity is ambiguous: {expected.key}")
    unless actual.base == expected.base do
      throw (drift s!"domain base drift for {expected.key}: expected \
        {repr expected.base}, received {repr actual.base}")
    unless actual.enumLabels == expected.enumLabels do
      throw (drift s!"enum labels drift for {expected.key}: expected \
        {repr expected.enumLabels}, received {repr actual.enumLabels}")
    unless actual.notNull == expected.notNull do
      throw (drift s!"domain nullability drift for {expected.key}: expected \
        {expected.notNull}, received {actual.notNull}")
    unless actual.arrayElement == expected.arrayElement do
      throw (drift s!"array element drift for {expected.key}: expected \
        {repr expected.arrayElement}, received {repr actual.arrayElement}")
    unless actual.arrayDelimiter == expected.arrayDelimiter do
      throw (drift s!"array delimiter drift for {expected.key}: expected \
        {repr expected.arrayDelimiter}, received {repr actual.arrayDelimiter}")
    unless actual.compositeFields == expected.compositeFields do
      throw (drift s!"composite fields drift for {expected.key}: expected \
        {repr expected.compositeFields}, received {repr actual.compositeFields}")
    unless actual.rangeSubtype == expected.rangeSubtype do
      throw (drift s!"range subtype drift for {expected.key}: expected \
        {repr expected.rangeSubtype}, received {repr actual.rangeSubtype}")
    unless actual.rangeMultirange == expected.rangeMultirange do
      throw (drift s!"range multirange drift for {expected.key}: expected \
        {repr expected.rangeMultirange}, received {repr actual.rangeMultirange}")
    unless actual.rangeCollation == expected.rangeCollation do
      throw (drift s!"range collation drift for {expected.key}: expected \
        {repr expected.rangeCollation}, received {repr actual.rangeCollation}")
    unless actual.rangeSubtypeOpclass == expected.rangeSubtypeOpclass do
      throw (drift s!"range subtype opclass drift for {expected.key}: expected \
        {repr expected.rangeSubtypeOpclass}, received {repr actual.rangeSubtypeOpclass}")
    unless actual.rangeCanonical == expected.rangeCanonical do
      throw (drift s!"range canonical routine drift for {expected.key}: expected \
        {repr expected.rangeCanonical}, received {repr actual.rangeCanonical}")
    unless actual.rangeSubtypeDiff == expected.rangeSubtypeDiff do
      throw (drift s!"range subtype-diff routine drift for {expected.key}: expected \
        {repr expected.rangeSubtypeDiff}, received {repr actual.rangeSubtypeDiff}")
    unless actual.multirangeRange == expected.multirangeRange do
      throw (drift s!"multirange range drift for {expected.key}: expected \
        {repr expected.multirangeRange}, received {repr actual.multirangeRange}")
    resolved := resolved.push {
      expected
      oid := actual.oid
      arrayOid := actual.arrayOid
    }
  pure resolved

private def checkColumns (relation : StaticRelationDesc) (actual : LiveRelation) :
    Except Error (Array ResolvedColumn) := do
  unless relation.columns.size == actual.columns.size do
    throw (drift s!"column count drift for {relation.key}: expected \
      {relation.columns.size}, received {actual.columns.size}")
  let mut resolved : Array ResolvedColumn := #[]
  for (expected, found) in relation.columns.zip actual.columns do
    unless expected.name == found.name do
      throw (drift s!"column name drift for {relation.key} at ordinal \
        {expected.ordinal}: expected {expected.name}, received {found.name}")
    unless expected.ordinal == found.attnum.toNat do
      throw (drift s!"column ordinal drift for {relation.key}.{expected.name}: expected \
        {expected.ordinal}, received {found.attnum}")
    unless expected.ty == found.ty do
      throw (drift s!"column type drift for {relation.key}.{expected.name}: expected \
        {repr expected.ty}, received {repr found.ty}")
    unless expected.nullable == found.nullable do
      throw (drift s!"column nullability drift for {relation.key}.{expected.name}: expected \
        {expected.nullable}, received {found.nullable}")
    resolved := resolved.push { expected, attnum := found.attnum }
  pure resolved

private def checkRelations (db : DatabaseDesc) (live : Array LiveRelation) :
    Except Error (Array ResolvedRelation) := do
  let mut resolved : Array ResolvedRelation := #[]
  for expected in db.relations do
    let foundMatches := live.filter (fun value => value.key == expected.key)
    let some actual := foundMatches[0]?
      | throw (drift s!"required PostgreSQL relation is missing: {expected.key}")
    if foundMatches.size != 1 then
      throw (drift s!"PostgreSQL relation identity is ambiguous: {expected.key}")
    unless actual.kind == expected.kind do
      throw (drift s!"relation kind drift for {expected.key}: expected \
        {repr expected.kind}, received {repr actual.kind}")
    resolved := resolved.push {
      expected
      oid := actual.oid
      columns := ← checkColumns expected actual
    }
  pure resolved

/-! ## Prepared statement cache

The cache publishes exactly one first-use owner per query key.  Other callers
receive the same promise and never prepare a duplicate named statement on the
physical connection.
-/

namespace Internal

/-- Runtime-internal cache state. Its name remains visible only because
module-mode `CheckedConnection` must expose the types of its private
representation fields. Applications must not construct or inspect it. -/
inductive PreparedEntryState (db : DatabaseDesc) where
  | pending (completion : IO.Promise (Except Error (PreparedQueryPlan db)))
  | ready (plan : PreparedQueryPlan db)
  /-- Descriptor drift is sticky: PostgreSQL has already installed the named
  statement, so retrying the same name would itself be a protocol error. -/
  | drifted (error : Error)

structure PreparedEntry (db : DatabaseDesc) where
  key : String
  state : PreparedEntryState db

abbrev PreparedCache (db : DatabaseDesc) := Std.Mutex (Array (PreparedEntry db))

inductive PrepareDecision (db : DatabaseDesc) where
  | ready (plan : PreparedQueryPlan db)
  | failed (error : Error)
  | owner
  | wait (completion : IO.Promise (Except Error (PreparedQueryPlan db)))

/-- A failed Parse/Describe request has not verified descriptor drift. Preserve
the underlying PostgreSQL error so transient failures remain retryable. -/
def preparationFailure (error : Pg.Error) : Error :=
  .postgres error

/-- Only a descriptor mismatch established after successful Parse/Describe is
sticky in the prepared-statement cache. -/
def isVerifiedDescriptorDrift : Error → Bool
  | .queryDrift _ => true
  | _ => false

end Internal

/-- A raw connection after its generated database contract has been checked.
The constructor is private; `attach` is the only way to obtain this capability. -/
structure CheckedConnection (db : DatabaseDesc) where
  private mk ::
  private rawValue : Pg.Connection
  private catalogValue : ResolvedCatalog db
  private preparedValue : Internal.PreparedCache db

/--
Access the underlying connection for transaction and lifecycle integration.

Mutating session/schema state or deallocating generated prepared statements can
invalidate this checked capability. Close the physical connection and attach a
new one afterward; bare reattachment cannot safely reconcile server-side
prepared-statement names with a fresh Lean cache.
-/
def CheckedConnection.raw (conn : CheckedConnection db) : Pg.Connection :=
  conn.rawValue

/-- The installation-local OIDs resolved during attachment. -/
def CheckedConnection.catalog (conn : CheckedConnection db) : ResolvedCatalog db :=
  conn.catalogValue

namespace Internal

/-- Runtime-only observation of a completed cached preparation. -/
def lookupPrepared (conn : CheckedConnection db) (key : String) :
    IO (Option Pg.Statement) :=
  conn.preparedValue.atomically do
    let entries ← get
    pure <| entries.findSome? fun entry =>
      if entry.key != key then none
      else match entry.state with
        | .ready plan => some plan.statement
        | .pending _ | .drifted _ => none

/-- Cache-level form used by the checked connection wrapper and focused tests.
A fresh physical connection owns a fresh value of this cache. -/
def beginPrepareCache (cache : PreparedCache db) (key : String) :
    IO (PrepareDecision db) :=
  cache.atomically do
    let entries ← get
    match entries.find? (fun entry => entry.key == key) with
    | some { state := .ready plan, .. } => pure (.ready plan)
    | some { state := .drifted error, .. } => pure (.failed error)
    | some { state := .pending completion, .. } => pure (.wait completion)
    | none =>
      let completion ← IO.Promise.new
      set (entries.push { key, state := .pending completion })
      pure .owner

/-- Claim preparation ownership, reuse a completed plan, or wait for the
caller that already owns this key. -/
def beginPrepare (conn : CheckedConnection db) (key : String) :
    IO (PrepareDecision db) :=
  beginPrepareCache conn.preparedValue key

/-- Publish the owner's result.  Descriptor drift stays sticky because the
named statement already exists; pre-Parse/transient failures are evicted so a
later call may retry.  Every result wakes current waiters. -/
def completePrepareCache (cache : PreparedCache db) (key : String)
    (result : Except Error (PreparedQueryPlan db)) (stickyFailure : Bool := false) :
    IO Unit := do
  let completion? ← cache.atomically do
    let entries ← get
    let some index := entries.findIdx? (fun entry => entry.key == key)
      | pure none
    let some entry := entries[index]?
      | pure none
    match entry.state with
    | .ready _ | .drifted _ => pure none
    | .pending completion =>
      match result with
      | .ok plan =>
        set (entries.set! index { key, state := .ready plan })
      | .error error =>
        if stickyFailure || isVerifiedDescriptorDrift error then
          set (entries.set! index { key, state := .drifted error })
        else
          set (entries.filter (fun value => value.key != key))
      pure (some completion)
  match completion? with
  | none => pure ()
  | some completion => discard <| completion.resolve result

/-- Publish a checked connection's preparation result. -/
def completePrepare (conn : CheckedConnection db) (key : String)
    (result : Except Error (PreparedQueryPlan db)) (stickyFailure : Bool := false) :
    IO Unit :=
  completePrepareCache conn.preparedValue key result stickyFailure

/-- Promote a ready plan to sticky drift after PostgreSQL execution or the
portal RowDescription proves that the cached descriptor contract changed. -/
def markPreparedCacheDrift (cache : PreparedCache db) (key : String)
    (error : Error) : IO Unit :=
  if !isVerifiedDescriptorDrift error then pure () else
    cache.atomically do
      let entries ← get
      let some index := entries.findIdx? (fun entry => entry.key == key)
        | return
      let some entry := entries[index]?
        | return
      match entry.state with
      | .ready _ =>
        set (entries.set! index { key, state := .drifted error })
      | .pending _ | .drifted _ => pure ()

/-- Checked-connection wrapper for sticky execution-time descriptor drift. -/
def markPreparedDrift (conn : CheckedConnection db) (key : String)
    (error : Error) : IO Unit :=
  markPreparedCacheDrift conn.preparedValue key error

end Internal

/-- Install the generated session contract and compare every relevant type,
relation, column, relational constraint/index, view, routine, and required
extension before constructing a checked capability. -/
def attach (db : DatabaseDesc) (conn : Pg.Connection) :
    Async (Except Error (CheckedConnection db)) := do
  let serverMajor ← match ← validateServerMajor db conn with
  | .error error => return .error error
  | .ok value => pure value
  match ← installSession db conn with
  | .error error => return .error error
  | .ok () => pure ()
  let liveTypes ← match ← loadTypes conn with
    | .error error => return .error error
    | .ok values => pure values
  let liveRelations ← match ← loadRelations conn with
    | .error error => return .error error
    | .ok values => pure values
  let relationalRelations := liveRelations.filter fun actual =>
    db.relations.any (fun expected => expected.key == actual.key)
  let liveIndexes ← match ← loadRelationalIndexes conn relationalRelations liveTypes with
    | .error error => return .error error
    | .ok values => pure values
  let liveConstraints ← match ← loadRelationalConstraints conn serverMajor
      relationalRelations liveTypes liveIndexes with
    | .error error => return .error error
    | .ok values => pure values
  let schemas := metadataSchemas db
  let liveViews ← match ← loadViews conn schemas with
    | .error error => return .error error
    | .ok values => pure values
  let liveRoutines ← match ← loadRoutines conn schemas liveTypes with
    | .error error => return .error error
    | .ok values => pure values
  let installedExtensions ← match ← loadExtensions conn with
    | .error error => return .error error
    | .ok values => pure values
  let extensionTypeOwnership ← match ← loadExtensionTypeOwnership conn liveTypes with
    | .error error => return .error error
    | .ok values => pure values
  let resolvedTypes ← match checkTypes db liveTypes with
    | .error error => return .error error
    | .ok values => pure values
  let resolvedRelations ← match checkRelations db liveRelations with
    | .error error => return .error error
    | .ok values => pure values
  match validateViewMetadata db.views liveViews with
  | .error error => return .error error
  | .ok () => pure ()
  match validateRoutineMetadata db.routines liveRoutines with
  | .error error => return .error error
  | .ok () => pure ()
  match validateIndexMetadata db.indexes (liveIndexes.map (fun value => value.ir)) with
  | .error error => return .error error
  | .ok () => pure ()
  match validateConstraintMetadata db.constraints liveConstraints with
  | .error error => return .error error
  | .ok () => pure ()
  match validateExtensionMetadata db installedExtensions extensionTypeOwnership with
  | .error error => return .error error
  | .ok () => pure ()
  let catalog ← match ResolvedCatalog.create db resolvedTypes resolvedRelations with
    | .error error => return .error error
    | .ok value => pure value
  pure (.ok (.mk conn catalog (← Std.Mutex.new #[])))

end Pgx.Typed
