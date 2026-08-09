import AppDb

/-!
# Live generated-runtime acceptance test

The caller owns PostgreSQL lifecycle and supplies an empty database plus the
ordered migration files.  This executable deliberately creates unrelated
user-defined types first so generated code cannot accidentally depend on the
OIDs observed during generation.
-/

namespace AppDb.RuntimeTest

open Std.Async

private structure Options where
  url : String
  migrations : Array String

private def usage : String :=
  "usage: app_db_runtime_test --url URL --migration PATH [--migration PATH ...]"

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

private def validatedEmail! (context value : String) :
    Async AppDb.Types.AppEmailAddress :=
  match AppDb.Types.AppEmailAddress.validate { toBase := value } with
  | .ok refined => pure refined
  | .error violation => fail s!"{context}: {violation}"

private def emailBase (email : AppDb.Types.AppEmailAddress) : String :=
  AppDb.Types.AppEmailAddress.toBase email

private def expectConstraintViolation (context expectedConstraint : String)
    (result : Except Pgx.Typed.Error α) : Async Unit :=
  match result with
  | .error (.constraintViolation (.checkFailed constraint)) =>
    unless constraint == expectedConstraint do
      fail s!"{context}: expected {expectedConstraint}, got {constraint}"
  | .error (.constraintViolation violation) =>
    fail s!"{context}: returned the wrong constraint violation: {violation}"
  | .error error => fail s!"{context}: returned the wrong error: {error}"
  | .ok _ => fail s!"{context}: unexpectedly decoded successfully"

private def verifyGeneratedNotValidMetadata : Async Unit := do
  let some constraint := AppDb.Constraints.all.find?
      (fun constraint => constraint.name == "users_organization_id_positive")
    | fail "generated metadata omitted the NOT VALID table constraint"
  unless constraint.kind == .check && !constraint.validated do
    fail "generated metadata did not preserve the NOT VALID table constraint"

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

private def installOidFillers (conn : Pg.Connection) : Async Unit := do
  let sql :=
    "CREATE SCHEMA lean_pgx_oid_filler; " ++
    "CREATE TYPE lean_pgx_oid_filler.filler_enum AS ENUM ('before', 'after'); " ++
    "CREATE TYPE lean_pgx_oid_filler.filler_record AS (value bigint, note text); " ++
    "CREATE DOMAIN lean_pgx_oid_filler.filler_domain AS text CHECK (VALUE <> '')"
  let _ ← pg! "create OID-shifting filler types" (← conn.exec sql)
  pure ()

private def replayMigrations (conn : Pg.Connection) (paths : Array String) :
    Async Unit := do
  for path in paths do
    let sql ← try
      IO.FS.readFile path
    catch error =>
      fail s!"read migration {path}: {error}"
    let _ ← pg! s!"apply migration {path}" (← conn.exec sql)

private def attach! (context : String) (conn : Pg.Connection) :
    Async (Pgx.Typed.CheckedConnection AppDb.database) := do
  typed! context (← AppDb.attach conn)

private def insertOrganization (conn : Pg.Connection) : Async Int64 := do
  let results ← pg! "insert organization" (← conn.query
    "INSERT INTO app.organizations (slug, display_name) \
     VALUES ('runtime-acceptance', 'Runtime Acceptance') RETURNING id")
  let some rows := results[0]?
    | fail "insert organization: no result set"
  unless results.size == 1 && rows.rows.size == 1 do
    fail s!"insert organization: expected one returned row, got \
      {results.size} result sets and {rows.rows.size} rows"
  match rows.get (α := Int64) 0 0 with
  | .ok id => pure id
  | .error error => fail s!"decode organization id: {error}"

private def exerciseGeneratedQueries
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (organizationId : Int64) : Async Unit := do
  let email := "runtime@example.com"
  let refinedEmail ← validatedEmail! "validate CreateUser email" email
  let command ← typed! "CreateUser.execute" (← AppDb.Queries.CreateUser.run conn {
    organizationId
    email := refinedEmail
    status := .active
    displayName := some "Runtime User"
  })
  unless command.tag == "INSERT 0 1" do
    fail s!"CreateUser.execute returned unexpected command tag {command.tag}"

  let listed ← typed! "ListUsers.many" (← AppDb.Queries.ListUsers.run conn {
    status := none
  })
  unless listed.size == 1 do
    fail s!"ListUsers.many returned {listed.size} rows; expected 1"
  let some listedUser := listed[0]?
    | fail "ListUsers.many returned no first row"
  unless listedUser.val.organizationId == organizationId &&
      emailBase listedUser.val.email == email && listedUser.val.status == .active &&
      listedUser.val.displayName == some "Runtime User" do
    fail "ListUsers.many decoded unexpected field values"

  let found? ← typed! "FindUserByEmail.zeroOrOne"
    (← AppDb.Queries.FindUserByEmail.run conn { email })
  let some found := found?
    | fail "FindUserByEmail.zeroOrOne returned none for the inserted user"
  unless found.val.organizationId == organizationId &&
      emailBase found.val.email == email && found.val.status == .active &&
      found.val.displayName == some "Runtime User" do
    fail "FindUserByEmail.zeroOrOne decoded unexpected field values"

  let exact ← typed! "GetUserById.exactlyOne"
    (← AppDb.Queries.GetUserById.run conn { id := found.val.id })
  unless exact.val.id == found.val.id && emailBase exact.val.email == email &&
      exact.val.status == .active do
    fail "GetUserById.exactlyOne decoded unexpected field values"

  let joined ← typed! "ListUsersWithProfile.many"
    (← AppDb.Queries.ListUsersWithProfile.run conn {})
  unless joined.size == 1 do
    fail s!"ListUsersWithProfile.many returned {joined.size} rows; expected 1"
  let some joinedUser := joined[0]?
    | fail "ListUsersWithProfile.many returned no first row"
  unless joinedUser.val.userId == some found.val.id &&
      joinedUser.val.email.map emailBase == some email &&
      joinedUser.val.profileBio.isNone && joinedUser.val.avatarUrl.isNone do
    fail "LEFT JOIN nullable decode produced unexpected field values"

  match ← AppDb.Queries.GetUserById.run conn { id := found.val.id + 1000000 } with
  | .error (.cardinality _ _) => pure ()
  | .error error =>
    fail s!"missing exactlyOne row returned the wrong error: {error}"
  | .ok _ =>
    fail "missing exactlyOne row unexpectedly decoded successfully"

private def exerciseNullableCheck
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (organizationId : Int64) : Async Unit := do
  let email := "nullable-check@example.com"
  let refinedEmail ← validatedEmail! "validate nullable-check email" email
  let command ← typed! "CreateUser.execute with nullable CHECK input"
    (← AppDb.Queries.CreateUser.run conn {
      organizationId
      email := refinedEmail
      status := .active
      displayName := none
    })
  unless command.tag == "INSERT 0 1" do
    fail s!"nullable CHECK insert returned unexpected command tag {command.tag}"
  let found? ← typed! "decode row whose nullable CHECK evaluates to unknown"
    (← AppDb.Queries.FindUserByEmail.run conn { email })
  let some found := found?
    | fail "nullable CHECK row was not returned"
  unless emailBase found.val.email == email && found.val.status == .active &&
      found.val.displayName.isNone do
    fail "nullable CHECK row decoded unexpected field values"

private def exerciseSelfJoinProvenance
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (organizationId : Int64) : Async Unit := do
  let leftEmail := "self-join-left@example.com"
  let rightEmail := "nullable-check@example.com"
  let refinedEmail ← validatedEmail! "validate self-join email" leftEmail
  let _ ← typed! "CreateUser.execute for self-join provenance"
    (← AppDb.Queries.CreateUser.run conn {
      organizationId
      email := refinedEmail
      status := .disabled
      displayName := some "Disabled User"
    })
  let mixed ← typed! "decode self-join fields from distinct source rows"
    (← AppDb.Queries.MixUserRows.run conn { leftEmail, rightEmail })
  unless mixed.val.leftStatus == .disabled && mixed.val.rightDisplayName.isNone do
    fail "self-join projection decoded unexpected field values"

private def exerciseStoredConstraintViolations
    (raw : Pg.Connection)
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (organizationId : Int64) : Async Unit := do
  let _ ← pg! "drop NOT VALID CHECK for invalid-row fixture" (← raw.exec
    "ALTER TABLE app.users DROP CONSTRAINT users_organization_id_positive")
  let _ ← pg! "insert negative organization key fixture" (← raw.exec
    "INSERT INTO app.organizations (id, slug, display_name) \
     OVERRIDING SYSTEM VALUE \
     VALUES (-1, 'negative-organization', 'Negative Organization')")
  let _ ← pg! "insert row violating generated NOT VALID CHECK" (← raw.exec
    "INSERT INTO app.users (organization_id, email, status, display_name) \
     VALUES (-1, 'invalid-positive@example.com', \
       'active'::app.user_status, 'Invalid Positive')")
  expectConstraintViolation "decode row violating generated NOT VALID CHECK"
    "users_organization_id_positive"
    (← AppDb.Queries.FindUserByEmail.run conn {
      email := "invalid-positive@example.com"
    })

  let _ ← pg! "drop table CHECK for invalid-row fixture" (← raw.exec
    "ALTER TABLE app.users DROP CONSTRAINT users_display_name_not_blank")
  let _ ← pg! "insert row violating generated table CHECK" (← raw.exec
    ("INSERT INTO app.users (organization_id, email, status, display_name) " ++
     "VALUES (" ++ toString organizationId ++
     ", 'invalid-row@example.com', 'active'::app.user_status, '   ')"))
  expectConstraintViolation "decode row violating generated table CHECK"
    "users_display_name_not_blank"
    (← AppDb.Queries.FindUserByEmail.run conn { email := "invalid-row@example.com" })

  let _ ← pg! "drop multi-column CHECK for invalid-row fixture" (← raw.exec
    "ALTER TABLE app.users DROP CONSTRAINT users_disabled_name_required")
  let _ ← pg! "insert row violating generated multi-column CHECK" (← raw.exec
    ("INSERT INTO app.users (organization_id, email, status, display_name) " ++
     "VALUES (" ++ toString organizationId ++
     ", 'invalid-multicol@example.com', 'disabled'::app.user_status, NULL)"))
  expectConstraintViolation "decode row violating generated multi-column CHECK"
    "users_disabled_name_required"
    (← AppDb.Queries.FindUserByEmail.run conn {
      email := "invalid-multicol@example.com"
    })

  let _ ← pg! "drop domain CHECK for invalid-domain fixture" (← raw.exec
    "ALTER DOMAIN app.email_address DROP CONSTRAINT email_address_shape")
  let _ ← pg! "insert row violating generated domain CHECK" (← raw.exec
    ("INSERT INTO app.users (organization_id, email, status, display_name) " ++
     "VALUES (" ++ toString organizationId ++
     ", 'x', 'active'::app.user_status, 'Invalid Domain')"))
  expectConstraintViolation "decode row violating generated domain CHECK"
    "email_address_shape"
    (← AppDb.Queries.FindUserByEmail.run conn { email := "x" })

private def expectQueryDrift
    (conn : Pgx.Typed.CheckedConnection AppDb.database) : Async Unit := do
  match ← AppDb.Queries.FindUserByEmail.run conn { email := "runtime@example.com" } with
  | .error (.queryDrift _) => pure ()
  | .error error => fail s!"post-DDL first preparation returned the wrong error: {error}"
  | .ok _ => fail "post-DDL first preparation unexpectedly succeeded"

private def expectSchemaDrift (conn : Pg.Connection) : Async Unit := do
  match ← AppDb.attach conn with
  | .error (.schemaDrift _) => pure ()
  | .error error => fail s!"fresh attachment returned the wrong error: {error}"
  | .ok _ => fail "fresh attachment unexpectedly accepted the drifted schema"

private def runAcceptance (options : Options) : Async Unit := do
  let config ← match Pg.ConnectConfig.parseUri options.url with
    | .ok value => pure value
    | .error error => fail s!"invalid PostgreSQL URL: {error}"
  withConnection config fun raw => do
    installOidFillers raw
    replayMigrations raw options.migrations
    verifyGeneratedNotValidMetadata
    let checked ← attach! "attach generated AppDb" raw
    let organizationId ← insertOrganization raw
    exerciseGeneratedQueries checked organizationId
    exerciseNullableCheck checked organizationId
    exerciseSelfJoinProvenance checked organizationId
    exerciseStoredConstraintViolations raw checked organizationId

    -- This physical connection is attached before the DDL change, but its
    -- prepared cache is intentionally untouched.  The next generated call
    -- must therefore compare a fresh Parse/Describe result against the old
    -- symbolic contract.
    withConnection config fun driftRaw => do
      let driftChecked ← attach! "attach query-drift connection" driftRaw
      let _ ← pg! "alter selected result column" (← raw.exec
        "ALTER TABLE app.users ALTER COLUMN display_name TYPE varchar(80)")
      expectQueryDrift driftChecked

      withConnection config fun freshRaw => do
        expectSchemaDrift freshRaw

private def asyncMain (args : List String) : Async UInt32 := do
  try
    let options ← match parseOptions args with
      | .ok value => pure value
      | .error error => fail error
    runAcceptance options
    IO.println "PASS AppDb generated runtime acceptance"
    pure 0
  catch error =>
    IO.eprintln s!"FAIL AppDb generated runtime acceptance: {error}"
    pure 1

def main (args : List String) : IO UInt32 :=
  Async.block (asyncMain args)

end AppDb.RuntimeTest

def main (args : List String) : IO UInt32 := AppDb.RuntimeTest.main args
