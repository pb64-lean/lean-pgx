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

private def numeric! (context value : String) : Async Pg.PgNumeric :=
  match Pg.PgNumeric.fromString value with
  | .ok parsed => pure parsed
  | .error error => fail s!"{context}: {error}"

private def plainTime! (context value : String) : Async Std.Time.PlainTime :=
  match Pg.PgDecode.decodeText Pg.Oid.time value with
  | .ok parsed => pure parsed
  | .error error => fail s!"{context}: {error}"

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

/-- A transient server failure during first preparation must not be classified
as descriptor drift or poison the checked connection's prepared cache. -/
private def exerciseTransientPrepareFailure
    (raw : Pg.Connection)
    (conn : Pgx.Typed.CheckedConnection AppDb.database) : Async Unit := do
  let _ ← pg! "begin transient-prepare fixture" (← raw.exec "BEGIN")
  match ← raw.exec "SELECT 1 / 0" with
  | .error _ => pure ()
  | .ok _ => fail "division-by-zero fixture unexpectedly succeeded"
  match ← AppDb.Queries.PrepareRetry.run conn {} with
  | .error (.postgres _) => pure ()
  | .error error =>
    fail s!"transient first prepare returned the wrong typed error: {error}"
  | .ok _ => fail "query unexpectedly prepared in an aborted transaction"
  let _ ← pg! "rollback transient-prepare fixture" (← raw.exec "ROLLBACK")
  let retried ← typed! "retry preparation after rollback"
    (← AppDb.Queries.PrepareRetry.run conn {})
  unless retried.val.value == some 42 do
    fail s!"retried query returned {retried.val.value}; expected some 42"

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

private def exerciseBroaderTypes
    (conn : Pgx.Typed.CheckedConnection AppDb.database) : Async Unit := do
  let primaryEmail ← validatedEmail! "validate composite email" "card@example.com"
  let secondaryEmail ← validatedEmail! "validate array email" "array@example.com"
  let statuses : AppDb.Types.AppUserStatusArray :=
    #[some .active, none, some .disabled]
  let emailData : AppDb.Types.AppEmailAddressArray.Data :=
    #[some primaryEmail, some secondaryEmail]
  let invalidEmailData : AppDb.Types.AppEmailAddressArray.Data :=
    #[some primaryEmail, none]
  match AppDb.Types.AppEmailAddressArray.validate invalidEmailData with
  | .error (.checkFailed "app._email_address (array) element domain NOT NULL") => pure ()
  | .error violation => fail s!"domain array returned the wrong violation: {violation}"
  | .ok _ => fail "domain array accepted a NULL element"
  let emails ← match AppDb.Types.AppEmailAddressArray.validate emailData with
    | .ok refined => pure refined
    | .error violation => fail s!"validate domain array fixture: {violation}"
  let cardData : AppDb.Types.AppContactCard.Data := {
    label := some "quoted, composite \\ value"
    status := some .active
    email := some primaryEmail
  }
  let oversizedCard : AppDb.Types.AppContactCard.Data := {
    cardData with label := some "12345678901234567890123456789012345678901"
  }
  match AppDb.Types.AppContactCard.validate oversizedCard with
  | .error (.checkFailed "app.contact_card (composite).label type modifier") => pure ()
  | .error violation => fail s!"composite typmod returned the wrong violation: {violation}"
  | .ok _ => fail "composite typmod accepted an oversized field"
  let missingEmailCard : AppDb.Types.AppContactCard.Data := {
    cardData with email := none
  }
  match AppDb.Types.AppContactCard.validate missingEmailCard with
  | .error (.checkFailed "app.contact_card (composite).email domain NOT NULL") => pure ()
  | .error violation => fail s!"composite domain returned the wrong violation: {violation}"
  | .ok _ => fail "composite accepted NULL for a NOT NULL domain field"
  let card ← match AppDb.Types.AppContactCard.validate cardData with
    | .ok refined => pure refined
    | .error violation => fail s!"validate composite typmod fixture: {violation}"
  let score : AppDb.Types.AppScoreRange :=
    .span (some { value := 10, inclusive := true })
      (some { value := 20, inclusive := false })
  let otherScore : AppDb.Types.AppScoreRange :=
    .span (some { value := 30, inclusive := true })
      (some { value := 40, inclusive := false })
  let scores : AppDb.Types.AppScoreMultirange := #[score, otherScore]
  let amount ← numeric! "parse numeric(6,2) fixture" "1234.50"
  let observedAt ← plainTime! "parse time(3) fixture" "12:34:56.789"
  let nickname := "MiXeD-Case"
  let aliases : AppDb.Types.AppCitext :=
    #[some "Primary", none, some "SECONDARY"]
  let labels : AppDb.Types.PgCatalogVarchar :=
    #[some "primary", none, some "backup"]

  let stored ← typed! "PutTypeSample.exactlyOne" (←
    AppDb.Queries.PutTypeSample.run conn {
      statuses, emails, card, score, scores, amount, observedAt, nickname, aliases, labels
    })
  unless stored.val.statuses == statuses do
    fail "enum array did not round-trip, including its NULL element"
  unless stored.val.emails.val.map (fun value => value.map emailBase) ==
      emails.val.map (fun value => value.map emailBase) do
    fail "domain array did not round-trip"
  unless stored.val.card.val.label == card.val.label &&
      stored.val.card.val.status == card.val.status &&
      stored.val.card.val.email.map emailBase == card.val.email.map emailBase do
    fail "composite value did not round-trip"
  unless stored.val.score == score && stored.val.scores == scores do
    fail "range or multirange did not round-trip"
  unless stored.val.amount.toString == "1234.50" &&
      stored.val.observedAt.toNanoseconds == observedAt.toNanoseconds do
    fail "numeric/time type-modifier values did not round-trip"
  unless stored.val.nickname == nickname && stored.val.aliases == aliases do
    fail "extension package scalar or nested array codec did not round-trip"
  unless stored.val.labels == labels do
    fail "array element type-modifier value did not round-trip"

  let summaries ← typed! "ListTypeSampleView.many" (←
    AppDb.Queries.ListTypeSampleView.run conn {})
  let some summary := summaries[0]?
    | fail "generated view query returned no row"
  unless summaries.size == 1 && summary.val.id == some stored.val.id &&
      summary.val.statusCount == some 3 &&
      summary.val.amount.map (·.toString) == some "1234.50" do
    fail "generated view query returned unexpected metadata-shaped values"

  let minimum ← numeric! "parse TVF minimum" "1000.00"
  let functionRows ← typed! "CallTypeSampleTvf.many" (←
    AppDb.Queries.CallTypeSampleTvf.run conn { minimum })
  let some functionRow := functionRows[0]?
    | fail "table-valued function query returned no row"
  unless functionRows.size == 1 &&
      functionRow.val.id == some stored.val.id &&
      functionRow.val.statusCount == some 3 do
    fail "table-valued function query returned unexpected values"

  unless AppDb.Constraints.views.size == 1 &&
      AppDb.Constraints.views.any (fun view =>
        view.relation == { schema := "app", name := "type_sample_summary" }) do
    fail "generated metadata did not isolate the application view"
  -- PostgreSQL adds constructor routines for named ranges and multiranges.
  -- Extension-owned implementation routines remain outside the application
  -- metadata contract even though the extension is installed in `app`.
  unless AppDb.Constraints.routines.any (fun routine =>
      routine.key.schema == "app" &&
      routine.key.name == "list_type_sample_summaries" &&
      routine.returnsSet &&
      routine.returnType == some {
        key := { schema := "app", name := "type_sample_summary", kind := .composite }
      } &&
      routine.resultColumns.map (·.name) == #["id", "status_count", "amount"]) &&
      AppDb.Constraints.routines.any (fun routine =>
        routine.key.schema == "app" && routine.key.name == "audit_int4_diff") &&
      !AppDb.Constraints.routines.any (fun routine =>
        routine.key.schema == "app" && routine.key.name == "citextin") do
    fail "generated metadata did not isolate the application table-valued function"
  unless AppDb.Constraints.extensionCodecPackages.any (fun package =>
      package.extension == "citext" && package.importModule == "AppDb.ExtensionCodecs" &&
      package.types == #[{ schema := "app", name := "citext", kind := .base }]) do
    fail "generated metadata omitted extension codec package provenance"

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

  -- Return the relation-constraint catalog to the generated contract before
  -- later fresh attachments.  The invalid rows have served their decoder
  -- tests and must be removed before the validated table constraints can be
  -- recreated.  This disposable fixture leaves the dropped domain CHECK in
  -- place: PostgreSQL cannot add it back while an array of that domain exists,
  -- and domain CHECKs are revalidated locally rather than attachment metadata.
  let _ ← pg! "remove invalid stored-check fixtures" (← raw.exec
    "DELETE FROM app.users WHERE email::text IN (\
      'invalid-positive@example.com', 'invalid-row@example.com', \
      'invalid-multicol@example.com', 'x')")
  let _ ← pg! "remove negative organization fixture" (← raw.exec
    "DELETE FROM app.organizations WHERE id = -1")
  let _ ← pg! "restore NOT VALID CHECK fixture" (← raw.exec
    "ALTER TABLE app.users \
      ADD CONSTRAINT users_organization_id_positive \
      CHECK (organization_id > 0) NOT VALID")
  let _ ← pg! "restore display-name CHECK fixture" (← raw.exec
    "ALTER TABLE app.users \
      ADD CONSTRAINT users_display_name_not_blank \
      CHECK (char_length(btrim(display_name)) > 0)")
  let _ ← pg! "restore multi-column CHECK fixture" (← raw.exec
    "ALTER TABLE app.users \
      ADD CONSTRAINT users_disabled_name_required \
      CHECK (status <> 'disabled'::app.user_status OR display_name IS NOT NULL)")

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

private def expectSchemaDriftContaining (expected : String)
    (conn : Pg.Connection) : Async Unit := do
  match ← AppDb.attach conn with
  | .error (.schemaDrift message) =>
      unless message.contains expected do
        fail s!"fresh attachment reported unrelated schema drift: {message}"
  | .error error => fail s!"fresh attachment returned the wrong error: {error}"
  | .ok _ => fail "fresh attachment unexpectedly accepted the drifted schema"

private def exerciseRelationalMetadataDrift
    (config : Pg.ConnectConfig) (raw : Pg.Connection) : Async Unit := do
  let _ ← pg! "drift foreign-key checking phase" (← raw.exec
    "ALTER TABLE app.user_profiles \
      ALTER CONSTRAINT user_profiles_user_fk INITIALLY IMMEDIATE")
  withConnection config (expectSchemaDriftContaining
    "constraint metadata drift for app.user_profiles.user_profiles_user_fk")
  let _ ← pg! "restore foreign-key checking phase" (← raw.exec
    "ALTER TABLE app.user_profiles \
      ALTER CONSTRAINT user_profiles_user_fk INITIALLY DEFERRED")
  withConnection config fun conn => do
    let _ ← attach! "reattach after restoring constraint metadata" conn
    pure ()

  let _ ← pg! "rename semantic unique index" (← raw.exec
    "ALTER INDEX app.users_email_key RENAME TO users_email_key_drifted")
  withConnection config (expectSchemaDriftContaining
    "required relational index metadata is missing")
  let _ ← pg! "restore semantic unique index name" (← raw.exec
    "ALTER INDEX app.users_email_key_drifted RENAME TO users_email_key")
  withConnection config fun conn => do
    let _ ← attach! "reattach after restoring semantic index metadata" conn
    pure ()

private def exerciseSemanticMetadataDrift
    (config : Pg.ConnectConfig) (raw : Pg.Connection) : Async Unit := do
  let _ ← pg! "drift application view definition" (← raw.exec
    "CREATE OR REPLACE VIEW app.type_sample_summary AS \
     SELECT sample.id, cardinality(sample.statuses) AS status_count, sample.amount \
     FROM app.type_samples AS sample WHERE sample.id IS NOT NULL")
  withConnection config (expectSchemaDriftContaining "view metadata drift")
  let _ ← pg! "restore application view definition" (← raw.exec
    "CREATE OR REPLACE VIEW app.type_sample_summary AS \
     SELECT sample.id, cardinality(sample.statuses) AS status_count, sample.amount \
     FROM app.type_samples AS sample")
  withConnection config fun conn => do
    let _ ← attach! "reattach after restoring view metadata" conn
    pure ()

  let _ ← pg! "drift table-valued function volatility" (← raw.exec
    "ALTER FUNCTION app.list_type_sample_summaries(numeric) VOLATILE")
  withConnection config (expectSchemaDriftContaining "routine metadata drift")
  let _ ← pg! "restore table-valued function volatility" (← raw.exec
    "ALTER FUNCTION app.list_type_sample_summaries(numeric) STABLE")
  withConnection config fun conn => do
    let _ ← attach! "reattach after restoring routine metadata" conn
    pure ()

private def exerciseRangeMetadataDrift
    (config : Pg.ConnectConfig) (raw : Pg.Connection) : Async Unit := do
  let _ ← pg! "drop range for subtype-diff drift" (← raw.exec
    "DROP TYPE app.audit_range")
  let _ ← pg! "recreate range without subtype-diff" (← raw.exec
    "CREATE TYPE app.audit_range AS RANGE (\
     subtype = integer, \
     multirange_type_name = app.audit_multirange)")
  withConnection config (expectSchemaDriftContaining
    "range subtype-diff routine drift")

  let _ ← pg! "drop drifted range" (← raw.exec
    "DROP TYPE app.audit_range")
  let _ ← pg! "restore range subtype-diff metadata" (← raw.exec
    "CREATE TYPE app.audit_range AS RANGE (\
     subtype = integer, \
     multirange_type_name = app.audit_multirange, \
     subtype_diff = app.audit_int4_diff)")

  let _ ← pg! "drop text range for collation drift" (← raw.exec
    "DROP TYPE app.audit_text_range")
  let _ ← pg! "recreate text range with another collation" (← raw.exec
    "CREATE TYPE app.audit_text_range AS RANGE (\
     subtype = text, \
     collation = pg_catalog.\"default\", \
     subtype_opclass = pg_catalog.text_ops, \
     multirange_type_name = app.audit_text_multirange)")
  withConnection config (expectSchemaDriftContaining "range collation drift")

  let _ ← pg! "drop text range for opclass drift" (← raw.exec
    "DROP TYPE app.audit_text_range")
  let _ ← pg! "recreate text range with another opclass" (← raw.exec
    "CREATE TYPE app.audit_text_range AS RANGE (\
     subtype = text, \
     collation = pg_catalog.\"C\", \
     subtype_opclass = pg_catalog.text_pattern_ops, \
     multirange_type_name = app.audit_text_multirange)")
  withConnection config (expectSchemaDriftContaining "range subtype opclass drift")

  let _ ← pg! "drop drifted text range" (← raw.exec
    "DROP TYPE app.audit_text_range")
  let _ ← pg! "restore text range metadata" (← raw.exec
    "CREATE TYPE app.audit_text_range AS RANGE (\
     subtype = text, \
     collation = pg_catalog.\"C\", \
     subtype_opclass = pg_catalog.text_ops, \
     multirange_type_name = app.audit_text_multirange)")
  withConnection config fun conn => do
    let _ ← attach! "reattach after restoring range metadata" conn
    pure ()

private def runAcceptance (options : Options) : Async Unit := do
  let config ← match Pg.ConnectConfig.parseUri options.url with
    | .ok value => pure value
    | .error error => fail s!"invalid PostgreSQL URL: {error}"
  withConnection config fun raw => do
    installOidFillers raw
    replayMigrations raw options.migrations
    verifyGeneratedNotValidMetadata
    let checked ← attach! "attach generated AppDb" raw
    exerciseTransientPrepareFailure raw checked
    let organizationId ← insertOrganization raw
    exerciseGeneratedQueries checked organizationId
    exerciseNullableCheck checked organizationId
    exerciseSelfJoinProvenance checked organizationId
    exerciseBroaderTypes checked
    exerciseRelationalMetadataDrift config raw
    exerciseSemanticMetadataDrift config raw
    exerciseRangeMetadataDrift config raw
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
