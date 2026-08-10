module

public import Pgx.Typed.Catalog
import Pg.Crypto.Sha256
import Pg.Crypto.Hex

public section

/-!
# Checked prepared-query execution

Every path verifies Parse/Describe metadata before binding and verifies the
portal RowDescription again before any generated decoder sees bytes.
-/

namespace Pgx.Typed

open Std.Async

private def queryKey (db : DatabaseDesc)
    (spec : QuerySpec db Params Row cardinality) : String :=
  Pg.Crypto.toHexLower <| Pg.Crypto.sha256
    (db.contractHash ++ "\n" ++ spec.contractHash ++ "\n" ++ spec.sql).toUTF8

private def statementName (key : String) : String :=
  "pgx_" ++ String.ofList (key.toList.take 48)

private def resolvedParamOids (catalog : ResolvedCatalog db)
    (params : Array ParamSpec) : Except Error (Array UInt32) :=
  params.mapM fun param => do
    pure (← catalog.resolveType param.ty.key).oid

private def executionFailure (error : Pg.Error) : Error :=
  match error with
  | .server fields =>
    if fields.sqlState? == some "0A000" &&
        (fields.message?.map (·.contains "cached plan")).getD false then
      .queryDrift (fields.message?.getD "cached plan changed its result type")
    else
      .postgres error
  | _ => .postgres error

private def prepareChecked (db : DatabaseDesc)
    (spec : QuerySpec db Params Row cardinality) (conn : CheckedConnection db) :
    Async (Except Error Pg.Statement) := do
  let key := queryKey db spec
  match ← Internal.beginPrepare conn key with
  | .ready statement => pure (.ok statement)
  | .failed error => pure (.error error)
  | .wait completion => await completion
  | .owner =>
    let result : Except Error Pg.Statement ← match
        resolvedParamOids conn.catalog spec.params with
      | .error error => pure (.error error)
      | .ok paramOids =>
        match ← Pg.Connection.prepare conn.raw (statementName key) spec.sql paramOids with
        | .error error => pure (.error (Internal.preparationFailure error))
        | .ok statement =>
          match verifyStatement conn.catalog spec.params spec.columns statement with
          | .error error => pure (.error error)
          | .ok () => pure (.ok statement)
    Internal.completePrepare conn key result
    pure result

private def runChecked (db : DatabaseDesc)
    (spec : QuerySpec db Params Row cardinality) (conn : CheckedConnection db)
    (params : Params) : Async (Except Error Pg.Rows) := do
  let statement ← match ← prepareChecked db spec conn with
    | .error error => return .error error
    | .ok statement => pure statement
  let encoded ← match spec.encode conn.catalog params with
    | .error error => return .error error
    | .ok encoded => pure encoded
  unless encoded.values.size == spec.params.size do
    return .error (.encode
      s!"generated encoder returned {encoded.values.size} values for {spec.params.size} parameters")
  unless encoded.formats.size == spec.params.size do
    return .error (.encode
      s!"generated encoder returned {encoded.formats.size} formats for {spec.params.size} parameters")
  for format in encoded.formats do
    unless format == 0 || format == 1 do
      return .error (.encode s!"unsupported PostgreSQL parameter format {format}")
  let rows ← match ← Pg.Connection.execute conn.raw statement.name
      encoded.values encoded.formats with
    | .error error => return .error (executionFailure error)
    | .ok rows => pure rows
  match verifyResultColumns conn.catalog spec.columns rows.columns with
  | .error error => pure (.error error)
  | .ok () => pure (.ok rows)

private def decodeRow (spec : QuerySpec db Params Row cardinality)
    (catalog : ResolvedCatalog db) (columns : Array Pg.Protocol.ColumnDesc)
    (values : Array (Option ByteArray)) : Except Error Row := do
  unless values.size == spec.columns.size do
    throw (.queryDrift
      s!"data row has {values.size} fields; expected {spec.columns.size}")
  spec.decode catalog columns values

/-- Execute a checked command that has no result columns. -/
def execute (spec : QuerySpec db Params Row .execute)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error CommandResult) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok rows =>
    if rows.rows.isEmpty then pure (.ok { tag := rows.tag })
    else pure (.error (.queryDrift
      s!"execute query unexpectedly returned {rows.rows.size} data rows"))

/-- Execute a checked query whose application contract requires one row. -/
def fetchOne (spec : QuerySpec db Params Row .exactlyOne)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error Row) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok rows =>
    match rows.rows with
    | #[values] => pure (decodeRow spec conn.catalog rows.columns values)
    | values => pure (.error (.cardinality "exactly one row" s!"{values.size} rows"))

/-- Execute a checked query whose application contract permits at most one
row. -/
def fetchOptional (spec : QuerySpec db Params Row .zeroOrOne)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error (Option Row)) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok rows =>
    match rows.rows with
    | #[] => pure (.ok none)
    | #[values] => pure (some <$> decodeRow spec conn.catalog rows.columns values)
    | values => pure (.error (.cardinality "zero or one row" s!"{values.size} rows"))

/-- Execute a checked query returning all buffered rows in server order. -/
def fetchMany (spec : QuerySpec db Params Row .many)
    (conn : CheckedConnection db) (params : Params) :
    Async (Except Error (Array Row)) := do
  match ← runChecked db spec conn params with
  | .error error => pure (.error error)
  | .ok rows =>
    pure (rows.rows.mapM (decodeRow spec conn.catalog rows.columns))

end Pgx.Typed
