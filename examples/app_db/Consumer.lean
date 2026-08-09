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
  email.toBase

def schemaUserEmail
    (user : AppDb.Schema.App.Users.Row) : AppDb.Types.AppEmailAddress :=
  user.email

def schemaUserStatus
    (user : AppDb.Schema.App.Users.Row) : AppDb.Types.AppUserStatus :=
  user.status

def schemaUserDisplayName
    (user : AppDb.Schema.App.Users.Row) : Option String :=
  user.displayName

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

def createEmptyRow : AppDb.Queries.CreateUser.Row :=
  AppDb.Queries.CreateUser.Row.mk

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
  row.id

def getUserOrganizationId (row : AppDb.Queries.GetUserById.Row) : Int64 :=
  row.organizationId

def getUserEmail (row : AppDb.Queries.GetUserById.Row) : String :=
  row.email

def getUserStatus
    (row : AppDb.Queries.GetUserById.Row) : AppDb.Types.AppUserStatus :=
  row.status

def getUserDisplayName
    (row : AppDb.Queries.GetUserById.Row) : Option String :=
  row.displayName

def getUserCreatedAt
    (row : AppDb.Queries.GetUserById.Row) : Std.Time.Timestamp :=
  row.createdAt

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
  row.id

def foundUserOrganizationId
    (row : AppDb.Queries.FindUserByEmail.Row) : Int64 :=
  row.organizationId

def foundUserEmail (row : AppDb.Queries.FindUserByEmail.Row) : String :=
  row.email

def foundUserStatus
    (row : AppDb.Queries.FindUserByEmail.Row) : AppDb.Types.AppUserStatus :=
  row.status

def foundUserDisplayName
    (row : AppDb.Queries.FindUserByEmail.Row) : Option String :=
  row.displayName

def foundUserCreatedAt
    (row : AppDb.Queries.FindUserByEmail.Row) : Std.Time.Timestamp :=
  row.createdAt

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
  row.id

def listedUserOrganizationId (row : AppDb.Queries.ListUsers.Row) : Int64 :=
  row.organizationId

def listedUserEmail (row : AppDb.Queries.ListUsers.Row) : String :=
  row.email

def listedUserStatus
    (row : AppDb.Queries.ListUsers.Row) : AppDb.Types.AppUserStatus :=
  row.status

def listedUserDisplayName
    (row : AppDb.Queries.ListUsers.Row) : Option String :=
  row.displayName

def listedUserCreatedAt
    (row : AppDb.Queries.ListUsers.Row) : Std.Time.Timestamp :=
  row.createdAt

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
  row.userId

def profileUserEmail
    (row : AppDb.Queries.ListUsersWithProfile.Row) : Option String :=
  row.email

def profileBio
    (row : AppDb.Queries.ListUsersWithProfile.Row) : Option String :=
  row.profileBio

def profileAvatarUrl
    (row : AppDb.Queries.ListUsersWithProfile.Row) : Option String :=
  row.avatarUrl

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

end AppDb.Consumer

def main : IO UInt32 := pure 0
