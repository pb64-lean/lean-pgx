import QuickstartDb

/-!
# lean-pgx quickstart

This small executable is also the live quickstart test. The test harness gives
it a fresh PostgreSQL URL and the declared migration paths.
-/

namespace Quickstart

open Std.Async

private structure Options where
  url : String
  migrations : Array String

private def usage : String :=
  "usage: quickstart --url URL --migration PATH [--migration PATH ...]"

private def parseMigrations (url : String) (paths : Array String) :
    List String → Except String Options
  | [] =>
    if paths.isEmpty then throw s!"at least one --migration is required\n{usage}"
    else pure { url, migrations := paths }
  | "--migration" :: path :: rest =>
    if path.isEmpty then throw s!"migration path must not be empty\n{usage}"
    else parseMigrations url (paths.push path) rest
  | _ => throw usage

private def parseOptions : List String → Except String Options
  | "--url" :: url :: rest =>
    if url.isEmpty then throw s!"URL must not be empty\n{usage}"
    else parseMigrations url #[] rest
  | _ => throw usage

private def fail (message : String) : Async α :=
  throw (IO.userError message)

private def pg! (context : String) (result : Except Pg.Error α) : Async α :=
  match result with
  | .ok value => pure value
  | .error error => fail s!"{context}: {error}"

private def typed! (context : String) (result : Except Pgx.Typed.Error α) : Async α :=
  match result with
  | .ok value => pure value
  | .error error => fail s!"{context}: {error}"

private def withConnection (config : Pg.ConnectConfig)
    (body : Pg.Connection → Async α) : Async α := do
  let conn ← Pg.connect config
  try
    let value ← body conn
    conn.close
    pure value
  catch error =>
    try conn.close catch _ => pure ()
    throw error

private def replayMigrations (conn : Pg.Connection) (paths : Array String) :
    Async Unit := do
  for path in paths do
    let sql ← IO.FS.readFile path
    let _ ← pg! s!"apply migration {path}" (← conn.exec sql)

private def runQuickstart (options : Options) : Async Unit := do
  let config ← match Pg.ConnectConfig.parseUri options.url with
    | .ok value => pure value
    | .error error => fail s!"invalid PostgreSQL URL: {error}"
  withConnection config fun raw => do
    replayMigrations raw options.migrations
    let _ ← pg! "insert example user" (← raw.exec
      "INSERT INTO app.users (email, display_name) VALUES ('ada@example.com', 'Ada')")
    let checked ← typed! "attach generated contract" (← QuickstartDb.attach raw)
    let some user ← typed! "run GetUser" (← QuickstartDb.Queries.GetUser.run checked { id := 1 })
      | fail "GetUser unexpectedly returned no row"
    unless QuickstartDb.Types.AppEmailAddress.toBase user.val.email == "ada@example.com" &&
        user.val.displayName == "Ada" do
      fail "GetUser decoded unexpected values"

private def asyncMain (args : List String) : Async UInt32 := do
  try
    let options ← match parseOptions args with
      | .ok value => pure value
      | .error error => fail error
    runQuickstart options
    IO.println "PASS lean-pgx quickstart"
    pure 0
  catch error =>
    IO.eprintln s!"FAIL lean-pgx quickstart: {error}"
    pure 1

def main (args : List String) : IO UInt32 :=
  Async.block (asyncMain args)

end Quickstart

def main (args : List String) : IO UInt32 := Quickstart.main args
