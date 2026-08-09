import AppDb

/-!
# Compile-time consumer of the generated AppDb API

These declarations intentionally spell out generated field and cardinality
types.  A selected-column removal, SQL type change, nullability change, or
cardinality change therefore breaks this module at elaboration time.
-/

namespace AppDb.Consumer

/-! Generated enum and domain branding. -/

def activeStatus : AppDb.Types.AppUserStatus :=
  .active

def statusLabel (status : AppDb.Types.AppUserStatus) : String :=
  status.toLabel

def emailBase (email : AppDb.Types.AppEmailAddress) : String :=
  AppDb.Types.AppEmailAddress.toBase email

def validateEmail
    (value : AppDb.Types.AppEmailAddress.Data) :
    Except Pgx.ConstraintViolation AppDb.Types.AppEmailAddress :=
  AppDb.Types.AppEmailAddress.validate value

theorem validateEmailSound
    {value : AppDb.Types.AppEmailAddress.Data}
    {refined : AppDb.Types.AppEmailAddress}
    (accepted : AppDb.Types.AppEmailAddress.validate value = .ok refined) :
    refined.val = value ∧ AppDb.Types.AppEmailAddress.ValidPred value :=
  AppDb.Types.AppEmailAddress.validate_sound accepted

theorem validateEmailComplete
    {value : AppDb.Types.AppEmailAddress.Data}
    (valid : AppDb.Types.AppEmailAddress.ValidPred value) :
    ∃ refined : AppDb.Types.AppEmailAddress,
      AppDb.Types.AppEmailAddress.validate value = .ok refined :=
  AppDb.Types.AppEmailAddress.validate_complete valid

def schemaUserEmail
    (user : AppDb.Schema.App.Users.Row) : AppDb.Types.AppEmailAddress :=
  user.val.email

def schemaUserStatus
    (user : AppDb.Schema.App.Users.Row) : AppDb.Types.AppUserStatus :=
  user.val.status

def schemaUserDisplayName
    (user : AppDb.Schema.App.Users.Row) : Option String :=
  user.val.displayName

def validateSchemaUser
    (value : AppDb.Schema.App.Users.Data) :
    Except Pgx.ConstraintViolation AppDb.Schema.App.Users.Row :=
  AppDb.Schema.App.Users.validate value

theorem validateSchemaUserSound
    {value : AppDb.Schema.App.Users.Data}
    {refined : AppDb.Schema.App.Users.Row}
    (accepted : AppDb.Schema.App.Users.validate value = .ok refined) :
    refined.val = value ∧ AppDb.Schema.App.Users.ValidPred value :=
  AppDb.Schema.App.Users.validate_sound accepted

theorem validateSchemaUserComplete
    {value : AppDb.Schema.App.Users.Data}
    (valid : AppDb.Schema.App.Users.ValidPred value) :
    ∃ refined : AppDb.Schema.App.Users.Row,
      AppDb.Schema.App.Users.validate value = .ok refined :=
  AppDb.Schema.App.Users.validate_complete valid

/-! `execute`: branded and nullable parameter fields, with no result row. -/

def createOrganizationId
    (params : AppDb.Queries.CreateUser.Params) : Int64 :=
  params.organizationId

def createEmail
    (params : AppDb.Queries.CreateUser.Params) : AppDb.Types.AppEmailAddress :=
  params.email

def createStatus
    (params : AppDb.Queries.CreateUser.Params) : AppDb.Types.AppUserStatus :=
  params.status

def createDisplayName
    (params : AppDb.Queries.CreateUser.Params) : Option String :=
  params.displayName

def createEmptyRow :
    Except Pgx.ConstraintViolation AppDb.Queries.CreateUser.Row :=
  AppDb.Queries.CreateUser.validate .mk

def createSpec :
    Pgx.Typed.QuerySpec AppDb.database
      AppDb.Queries.CreateUser.Params
      AppDb.Queries.CreateUser.Row
      .execute :=
  AppDb.Queries.CreateUser.spec

def runCreate
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (params : AppDb.Queries.CreateUser.Params) :
    Std.Async.Async (Except Pgx.Typed.Error Pgx.Typed.CommandResult) :=
  AppDb.Queries.CreateUser.run conn params

/-! `exactlyOne`: every selected column is pinned to its generated field type. -/

def getUserIdParam
    (params : AppDb.Queries.GetUserById.Params) : Int64 :=
  params.id

def getUserId (row : AppDb.Queries.GetUserById.Row) : Int64 :=
  row.val.id

def getUserOrganizationId (row : AppDb.Queries.GetUserById.Row) : Int64 :=
  row.val.organizationId

def getUserEmail
    (row : AppDb.Queries.GetUserById.Row) : AppDb.Types.AppEmailAddress :=
  row.val.email

def getUserStatus
    (row : AppDb.Queries.GetUserById.Row) : AppDb.Types.AppUserStatus :=
  row.val.status

def getUserDisplayName
    (row : AppDb.Queries.GetUserById.Row) : Option String :=
  row.val.displayName

def getUserCreatedAt
    (row : AppDb.Queries.GetUserById.Row) : Std.Time.Timestamp :=
  row.val.createdAt

def getUserSpec :
    Pgx.Typed.QuerySpec AppDb.database
      AppDb.Queries.GetUserById.Params
      AppDb.Queries.GetUserById.Row
      .exactlyOne :=
  AppDb.Queries.GetUserById.spec

def runGetUser
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (params : AppDb.Queries.GetUserById.Params) :
    Std.Async.Async (Except Pgx.Typed.Error AppDb.Queries.GetUserById.Row) :=
  AppDb.Queries.GetUserById.run conn params

/-! `zeroOrOne`: parameter and every selected result field are pinned. -/

def findUserEmailParam
    (params : AppDb.Queries.FindUserByEmail.Params) : String :=
  params.email

def foundUserId (row : AppDb.Queries.FindUserByEmail.Row) : Int64 :=
  row.val.id

def foundUserOrganizationId
    (row : AppDb.Queries.FindUserByEmail.Row) : Int64 :=
  row.val.organizationId

def foundUserEmail
    (row : AppDb.Queries.FindUserByEmail.Row) : AppDb.Types.AppEmailAddress :=
  row.val.email

def foundUserStatus
    (row : AppDb.Queries.FindUserByEmail.Row) : AppDb.Types.AppUserStatus :=
  row.val.status

def foundUserDisplayName
    (row : AppDb.Queries.FindUserByEmail.Row) : Option String :=
  row.val.displayName

def foundUserCreatedAt
    (row : AppDb.Queries.FindUserByEmail.Row) : Std.Time.Timestamp :=
  row.val.createdAt

def validateFoundUser
    (value : AppDb.Queries.FindUserByEmail.RowData) :
    Except Pgx.ConstraintViolation AppDb.Queries.FindUserByEmail.Row :=
  AppDb.Queries.FindUserByEmail.validate value

theorem validateFoundUserSound
    {value : AppDb.Queries.FindUserByEmail.RowData}
    {refined : AppDb.Queries.FindUserByEmail.Row}
    (accepted : AppDb.Queries.FindUserByEmail.validate value = .ok refined) :
    refined.val = value ∧ AppDb.Queries.FindUserByEmail.ValidPred value :=
  AppDb.Queries.FindUserByEmail.validate_sound accepted

theorem validateFoundUserComplete
    {value : AppDb.Queries.FindUserByEmail.RowData}
    (valid : AppDb.Queries.FindUserByEmail.ValidPred value) :
    ∃ refined : AppDb.Queries.FindUserByEmail.Row,
      AppDb.Queries.FindUserByEmail.validate value = .ok refined :=
  AppDb.Queries.FindUserByEmail.validate_complete valid

def findUserSpec :
    Pgx.Typed.QuerySpec AppDb.database
      AppDb.Queries.FindUserByEmail.Params
      AppDb.Queries.FindUserByEmail.Row
      .zeroOrOne :=
  AppDb.Queries.FindUserByEmail.spec

def runFindUser
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (params : AppDb.Queries.FindUserByEmail.Params) :
    Std.Async.Async
      (Except Pgx.Typed.Error (Option AppDb.Queries.FindUserByEmail.Row)) :=
  AppDb.Queries.FindUserByEmail.run conn params

/-! `many`: nullable enum input and every selected result field are pinned. -/

def listUsersStatusParam
    (params : AppDb.Queries.ListUsers.Params) :
    Option AppDb.Types.AppUserStatus :=
  params.status

def listedUserId (row : AppDb.Queries.ListUsers.Row) : Int64 :=
  row.val.id

def listedUserOrganizationId (row : AppDb.Queries.ListUsers.Row) : Int64 :=
  row.val.organizationId

def listedUserEmail
    (row : AppDb.Queries.ListUsers.Row) : AppDb.Types.AppEmailAddress :=
  row.val.email

def listedUserStatus
    (row : AppDb.Queries.ListUsers.Row) : AppDb.Types.AppUserStatus :=
  row.val.status

def listedUserDisplayName
    (row : AppDb.Queries.ListUsers.Row) : Option String :=
  row.val.displayName

def listedUserCreatedAt
    (row : AppDb.Queries.ListUsers.Row) : Std.Time.Timestamp :=
  row.val.createdAt

def listUsersSpec :
    Pgx.Typed.QuerySpec AppDb.database
      AppDb.Queries.ListUsers.Params
      AppDb.Queries.ListUsers.Row
      .many :=
  AppDb.Queries.ListUsers.spec

def runListUsers
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (params : AppDb.Queries.ListUsers.Params) :
    Std.Async.Async
      (Except Pgx.Typed.Error (Array AppDb.Queries.ListUsers.Row)) :=
  AppDb.Queries.ListUsers.run conn params

/-! LEFT JOIN projections: conservative analysis currently makes every result
field optional, including fields projected from the preserved side. -/

def profileListParams : AppDb.Queries.ListUsersWithProfile.Params :=
  AppDb.Queries.ListUsersWithProfile.Params.mk

def profileUserId
    (row : AppDb.Queries.ListUsersWithProfile.Row) : Option Int64 :=
  row.val.userId

def profileUserEmail
    (row : AppDb.Queries.ListUsersWithProfile.Row) :
    Option AppDb.Types.AppEmailAddress :=
  row.val.email

def profileBio
    (row : AppDb.Queries.ListUsersWithProfile.Row) : Option String :=
  row.val.profileBio

def profileAvatarUrl
    (row : AppDb.Queries.ListUsersWithProfile.Row) : Option String :=
  row.val.avatarUrl

def listProfilesSpec :
    Pgx.Typed.QuerySpec AppDb.database
      AppDb.Queries.ListUsersWithProfile.Params
      AppDb.Queries.ListUsersWithProfile.Row
      .many :=
  AppDb.Queries.ListUsersWithProfile.spec

def runListProfiles
    (conn : Pgx.Typed.CheckedConnection AppDb.database)
    (params : AppDb.Queries.ListUsersWithProfile.Params) :
    Std.Async.Async
      (Except Pgx.Typed.Error
        (Array AppDb.Queries.ListUsersWithProfile.Row)) :=
  AppDb.Queries.ListUsersWithProfile.run conn params

/-! Milestone-3 containers, composites, type modifiers, views, and routines. -/

def typeSampleStatuses
    (params : AppDb.Queries.PutTypeSample.Params) :
    AppDb.Types.AppUserStatus_2 :=
  params.statuses

def typeSampleEmails
    (params : AppDb.Queries.PutTypeSample.Params) :
    AppDb.Types.AppEmailAddress_2 :=
  params.emails

def typeSampleCard
    (params : AppDb.Queries.PutTypeSample.Params) :
    AppDb.Types.AppContactCard :=
  params.card

def typeSampleScore
    (params : AppDb.Queries.PutTypeSample.Params) :
    AppDb.Types.AppScoreRange :=
  params.score

def typeSampleScores
    (params : AppDb.Queries.PutTypeSample.Params) :
    AppDb.Types.AppScoreMultirange :=
  params.scores

def typeSampleAmount
    (row : AppDb.Queries.PutTypeSample.Row) : Pg.PgNumeric :=
  row.val.amount

def typeSampleObservedAt
    (row : AppDb.Queries.PutTypeSample.Row) : Std.Time.PlainTime :=
  row.val.observedAt

def typeSampleNickname
    (row : AppDb.Queries.PutTypeSample.Row) : String :=
  row.val.nickname

def typeSampleAliases
    (row : AppDb.Queries.PutTypeSample.Row) : AppDb.Types.AppCitext :=
  row.val.aliases

def typeSampleCardStatus
    (card : AppDb.Types.AppContactCard) : Option AppDb.Types.AppUserStatus :=
  card.status

def summaryViewAmount
    (row : AppDb.Queries.ListTypeSampleView.Row) : Option Pg.PgNumeric :=
  row.val.amount

def summaryFunctionAmount
    (row : AppDb.Queries.CallTypeSampleTvf.Row) : Option Pg.PgNumeric :=
  row.val.amount

def generatedViews : Array Pgx.ViewIR :=
  AppDb.Constraints.views

def generatedRoutines : Array Pgx.RoutineIR :=
  AppDb.Constraints.routines

end AppDb.Consumer

def main : IO UInt32 := pure 0
