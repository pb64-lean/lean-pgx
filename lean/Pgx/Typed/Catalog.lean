import Pgx.Typed.Descriptors
import Pg.Connection

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
    Async (Except Error Unit) := do
  match ← currentSetting conn "server_version_num" with
  | .error error => pure (.error error)
  | .ok version =>
    match parseNat "server_version_num" version with
    | .error error => pure (.error error)
    | .ok versionNumber =>
      let major := versionNumber / 10000
      if db.serverMajors.contains major then
        pure (.ok ())
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
  kindSql "rrt" ++ " END " ++
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
  pure {
    key := { schema, name, kind }, oid, arrayOid, base, notNull,
    arrayElement, arrayDelimiter, rangeSubtype, rangeMultirange, multirangeRange
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
  "(NOT (a.attnotnull OR t.typnotnull))::text " ++
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
  pure ({ schema := relationSchema, name := relationName }, {
    name, attnum, ty := { key := { schema := typeSchema, name := typeName, kind := typeKind }, typmod },
    nullable
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
    (installed : Array (String × String)) : Except Error Unit := do
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

private inductive PreparedEntryState where
  | pending (completion : IO.Promise (Except Error Pg.Statement))
  | ready (statement : Pg.Statement)
  /-- Descriptor drift is sticky: PostgreSQL has already installed the named
  statement, so retrying the same name would itself be a protocol error. -/
  | drifted (error : Error)

private structure PreparedEntry where
  key : String
  state : PreparedEntryState

private abbrev PreparedCache := Std.Mutex (Array PreparedEntry)

inductive PrepareDecision where
  | ready (statement : Pg.Statement)
  | failed (error : Error)
  | owner
  | wait (completion : IO.Promise (Except Error Pg.Statement))

/-- A raw connection after its generated database contract has been checked.
The constructor is private; `attach` is the only way to obtain this capability. -/
structure CheckedConnection (db : DatabaseDesc) where
  private mk ::
  private rawValue : Pg.Connection
  private catalogValue : ResolvedCatalog db
  private preparedValue : PreparedCache

/-- Access the underlying connection for verified generated operations. -/
def CheckedConnection.raw (conn : CheckedConnection db) : Pg.Connection :=
  conn.rawValue

/-- The installation-local OIDs resolved during attachment. -/
def CheckedConnection.catalog (conn : CheckedConnection db) : ResolvedCatalog db :=
  conn.catalogValue

/-- Observe a completed cached preparation without claiming first-use ownership. -/
def CheckedConnection.lookupPrepared (conn : CheckedConnection db) (key : String) :
    IO (Option Pg.Statement) :=
  conn.preparedValue.atomically do
    let entries ← get
    pure <| entries.findSome? fun entry =>
      if entry.key != key then none
      else match entry.state with
        | .ready statement => some statement
        | .pending _ | .drifted _ => none

/-- Claim preparation ownership, reuse a completed statement, or wait for the
caller that already owns this key. -/
def CheckedConnection.beginPrepare (conn : CheckedConnection db) (key : String) :
    IO PrepareDecision :=
  conn.preparedValue.atomically do
    let entries ← get
    match entries.find? (fun entry => entry.key == key) with
    | some { state := .ready statement, .. } => pure (.ready statement)
    | some { state := .drifted error, .. } => pure (.failed error)
    | some { state := .pending completion, .. } => pure (.wait completion)
    | none =>
      let completion ← IO.Promise.new
      set (entries.push { key, state := .pending completion })
      pure .owner

/-- Publish the owner's result.  Descriptor drift stays sticky because the
named statement already exists; pre-Parse/transient failures are evicted so a
later call may retry.  Every result wakes current waiters. -/
def CheckedConnection.completePrepare (conn : CheckedConnection db) (key : String)
    (result : Except Error Pg.Statement) : IO Unit := do
  let completion? ← conn.preparedValue.atomically do
    let entries ← get
    let some index := entries.findIdx? (fun entry => entry.key == key)
      | pure none
    let some entry := entries[index]?
      | pure none
    match entry.state with
    | .ready _ | .drifted _ => pure none
    | .pending completion =>
      match result with
      | .ok statement =>
        set (entries.set! index { key, state := .ready statement })
      | .error error@(.queryDrift _) =>
        set (entries.set! index { key, state := .drifted error })
      | .error _ =>
        set (entries.filter (fun value => value.key != key))
      pure (some completion)
  match completion? with
  | none => pure ()
  | some completion => discard <| completion.resolve result

/-- Install the generated session contract and compare every relevant type,
relation, column, view, routine, and required extension before constructing a
checked capability. -/
def attach (db : DatabaseDesc) (conn : Pg.Connection) :
    Async (Except Error (CheckedConnection db)) := do
  match ← validateServerMajor db conn with
  | .error error => return .error error
  | .ok () => pure ()
  match ← installSession db conn with
  | .error error => return .error error
  | .ok () => pure ()
  let liveTypes ← match ← loadTypes conn with
    | .error error => return .error error
    | .ok values => pure values
  let liveRelations ← match ← loadRelations conn with
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
  match validateExtensionMetadata db installedExtensions with
  | .error error => return .error error
  | .ok () => pure ()
  let catalog ← match ResolvedCatalog.create db resolvedTypes resolvedRelations with
    | .error error => return .error error
    | .ok value => pure value
  pure (.ok (.mk conn catalog (← Std.Mutex.new #[])))

end Pgx.Typed
