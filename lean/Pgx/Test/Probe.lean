import Pgx.Codegen.Probe

namespace Pgx.Test.Probe

open Pgx.Codegen.Probe

private def validConfig : Config := {
  schemas := #["app"]
  session := { searchPath := #["app", "pg_catalog"] }
  supportedServerMajors := #[18, 17]
  queries := #[{
    name := "GetUser"
    sql := "SELECT id FROM app.users WHERE id = $1"
    cardinality := .zeroOrOne
    parameters := #[{ position := 1, name := "id", nullable := false }]
  }]
}

private def citextKey : Pgx.TypeKey := {
  schema := "public", name := "citext", kind := .base
}

private def vectorKey : Pgx.TypeKey := {
  schema := "public", name := "vector", kind := .base
}

private def halfvecKey : Pgx.TypeKey := {
  schema := "public", name := "halfvec", kind := .base
}

private def citextArrayKey : Pgx.TypeKey := {
  schema := "public", name := "_citext", kind := .array
}

private def overrideFor (key : Pgx.TypeKey) (leanType codec moduleName : String) :
    Pgx.TypeOverrideIR := {
  key, leanType, codec, importModule := some moduleName
}

private def packageConfig : Config := {
  validConfig with
  requiredExtensions := #["vector", "citext"]
  typeOverrides := #[
    overrideFor vectorKey "Vector" "vectorCodec" "Ext.Vector",
    overrideFor halfvecKey "HalfVector" "halfvecCodec" "Ext.Vector",
    overrideFor citextKey "String" "citextCodec" "Ext.Citext"
  ]
  extensionCodecPackages := #[
    {
      extension := "vector"
      importModule := "Ext.Vector"
      types := #[vectorKey, halfvecKey]
    },
    {
      extension := "citext"
      importModule := "Ext.Citext"
      types := #[citextKey]
    }
  ]
}

private def isError : Except Error α → Bool
  | .error _ => true
  | .ok _ => false

private def relation : Pgx.RelationKey := { schema := "app", name := "users" }

private def textType : Pgx.TypeRef := {
  key := { schema := "pg_catalog", name := "text", kind := .base }
}

private def intType : Pgx.TypeRef := {
  key := { schema := "pg_catalog", name := "int4", kind := .base }
}

private def trimmedKey : Pgx.TypeKey := {
  schema := "app", name := "trimmed_text", kind := .domain
}

private def emailKey : Pgx.TypeKey := {
  schema := "app", name := "email_address", kind := .domain
}

private def domainMetadata : Array Pgx.DomainIR := #[
  { key := trimmedKey, base := textType, notNull := false },
  { key := emailKey, base := { key := trimmedKey }, notNull := true }
]

private def emailColumn : Pgx.RelationColumnIR := {
  name := "email"
  ordinal := 1
  ty := { key := emailKey }
  nullable := false
}

private def commonConstraint : Pgx.ConstraintIR := {
  relation
  name := "users_pkey"
  kind := .primaryKey
  columns := #["id"]
}

private def nativeNotNull : Pgx.ConstraintIR := {
  relation
  name := "users_email_required"
  kind := .notNull
  columns := #["email"]
}

private def attributeNotNull : Array AttributeNotNull := #[
  { relation, column := "email" },
  { relation, column := "id" }
]

private def innerPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Hash Join\",\"Join Type\":\"Inner\"," ++
  "\"Plans\":[{\"Node Type\":\"Seq Scan\"},{\"Node Type\":\"Hash\"," ++
  "\"Plans\":[{\"Node Type\":\"Index Scan\"}]}]}}]"

private def leftPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Nested Loop\",\"Join Type\":\"Left\"," ++
  "\"Plans\":[{\"Node Type\":\"Seq Scan\"},{\"Node Type\":\"Index Scan\"}]}}]"

private def fullPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Aggregate\",\"Plans\":[{" ++
  "\"Node Type\":\"Merge Join\",\"Join Type\":\"Full\"," ++
  "\"Plans\":[{\"Node Type\":\"Sort\"},{\"Node Type\":\"Sort\"}]}]}}]"

private def singleRelationPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Seq Scan\",\"Schema\":\"app\"," ++
  "\"Relation Name\":\"users\",\"Alias\":\"u\"}}]"

private def selfJoinPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Nested Loop\",\"Join Type\":\"Inner\"," ++
  "\"Plans\":[{\"Node Type\":\"Seq Scan\",\"Schema\":\"app\"," ++
  "\"Relation Name\":\"users\",\"Alias\":\"left_user\"}," ++
  "{\"Node Type\":\"Index Scan\",\"Schema\":\"app\"," ++
  "\"Relation Name\":\"users\",\"Alias\":\"right_user\"}]}}]"

private def twoRelationPlan : String :=
  "[{\"Plan\":{\"Node Type\":\"Hash Join\",\"Join Type\":\"Inner\"," ++
  "\"Plans\":[{\"Node Type\":\"Seq Scan\",\"Schema\":\"app\"," ++
  "\"Relation Name\":\"users\",\"Alias\":\"u\"}," ++
  "{\"Node Type\":\"Hash\",\"Plans\":[{\"Node Type\":\"Seq Scan\"," ++
  "\"Schema\":\"app\",\"Relation Name\":\"profiles\"," ++
  "\"Alias\":\"p\"}]}]}}]"

private def checkRelationalCatalogAdapters : IO Unit := do
  assert! !Pg17.adapter.supportsNativeNotNull
  assert! Pg18.adapter.supportsNativeNotNull
  assert! !Pg17.adapter.supportsConstraintEnforcement
  assert! Pg18.adapter.supportsConstraintEnforcement
  assert! !Pg17.adapter.supportsTemporalConstraints
  assert! Pg18.adapter.supportsTemporalConstraints
  assert! !Pg17.adapter.constraintTypeTags.contains "n"
  assert! Pg18.adapter.constraintTypeTags.contains "n"
  for adapter in #[Pg17.adapter, Pg18.adapter] do
    let sql := adapter.constraintCatalogSql
    assert! sql.contains "pg_catalog.pg_depend"
    assert! sql.contains "pg_catalog.pg_proc"
    assert! sql.contains "pg_catalog.pg_operator"
    assert! sql.contains "pg_catalog.pg_constraint'::pg_catalog.regclass"
    assert! sql.contains "con.condeferrable"
    assert! sql.contains "con.condeferred"
    assert! sql.contains "con.conparentid"
    assert! sql.contains "con.conislocal"
    assert! sql.contains "con.coninhcount"
    assert! sql.contains "con.connoinherit"
    assert! sql.contains "con.confmatchtype"
    assert! sql.contains "con.confupdtype"
    assert! sql.contains "con.confdeltype"
    assert! sql.contains "i.indnullsnotdistinct"
  assert! !Pg17.adapter.constraintCatalogSql.contains "con.conenforced"
  assert! !Pg17.adapter.constraintCatalogSql.contains "con.conperiod"
  assert! Pg18.adapter.constraintCatalogSql.contains "con.conenforced"
  assert! Pg18.adapter.constraintCatalogSql.contains "con.conperiod"
  assert! Adapter.constraintDeleteSetColumnSql.contains "con.confdelsetcols"
  assert! Adapter.constraintOperatorSql.contains "con.conpfeqop"
  assert! Adapter.constraintOperatorSql.contains "con.conppeqop"
  assert! Adapter.constraintOperatorSql.contains "con.conffeqop"
  assert! Adapter.constraintOperatorSql.contains "con.conexclop"

private def checkUnsafeNativeNotNullRejection : IO Unit := do
  let unsafeNative : Pgx.ConstraintIR := {
    nativeNotNull with
    enforced := false
    validated := false
    parent := some {
      relation := { schema := "app", name := "parent_users" }
      name := "parent_email_required"
    }
    isLocal := false
    inheritanceCount := 1
    noInherit := true
  }
  match Pg18.adapter.normalizeConstraints #[unsafeNative]
      #[{ relation, column := "email" }] with
  | .error message =>
      assert! message.contains "must be enforced and validated"
  | .ok _ => panic! "PostgreSQL 18 accepted an unsafe native NOT NULL constraint"
  match Pg18.adapter.normalizeConstraints
      #[{ nativeNotNull with validated := false }]
      #[{ relation, column := "email" }] with
  | .error message =>
      assert! message.contains "must be enforced and validated"
  | .ok _ => panic! "PostgreSQL 18 accepted an unvalidated native NOT NULL constraint"
  let collidingCheck : Pgx.ConstraintIR := {
    relation
    name := "<not-null:email>"
    kind := .check
  }
  match Pg18.adapter.normalizeConstraints #[collidingCheck, nativeNotNull]
      #[{ relation, column := "email" }] with
  | .error message =>
      assert! message.contains "duplicate normalized constraint identity"
  | .ok _ => panic! "synthetic NOT NULL identity collision was accepted"

def main : IO UInt32 := do
  assert! (validateConfig validConfig).isOk
  assert! (validateConfig packageConfig).isOk
  assert! validConfig.normalizedSupportedServerMajors == #[17, 18]
  assert! (adapterForServerMajor? 17).map (·.serverMajor) == some 17
  assert! (adapterForServerMajor? 18).map (·.serverMajor) == some 18
  assert! (adapterForServerMajor? 16).isNone
  match logicalTypeForDirectProjection domainMetadata "GetUser" "email"
      emailColumn textType with
  | .ok logical => assert! logical == some emailColumn.ty
  | .error error => panic! toString error
  assert! isError (logicalTypeForDirectProjection domainMetadata "GetUser" "email"
    emailColumn intType)
  match logicalTypeForDirectProjection domainMetadata "GetUser" "age"
      { emailColumn with name := "age", ty := intType } intType with
  | .ok logical => assert! logical.isNone
  | .error error => panic! toString error
  let unsupportedSource := "CHECK (lower(age) > 0)"
  let unsupportedDiagnostic : Pgx.Constraint.Diagnostic := {
    category := .unsupportedFunction
    offset := 7
    message := "function lower is not supported in local constraints"
  }
  let rendered := toString (Error.unsupportedConstraint "app.users"
    "users_age_check" unsupportedSource unsupportedDiagnostic)
  assert! rendered.contains "app.users"
  assert! rendered.contains "users_age_check"
  assert! rendered.contains "category=unsupported-function"
  assert! rendered.contains "offset=7"
  assert! rendered.contains unsupportedSource
  checkRelationalCatalogAdapters
  let dependencySource := "CHECK (btrim(display_name) <> '')"
  match validateLocalConstraintDependencies "app.users" "name_check"
      dependencySource true false with
  | .error (.unsupportedConstraint owner name source diagnostic) => do
      assert! owner == "app.users"
      assert! name == "name_check"
      assert! source == dependencySource
      assert! diagnostic.category == .unsupportedFunction
      assert! diagnostic.offset == 0
      assert! diagnostic.message ==
        "catalog-dependent functions are unsupported in local constraints"
  | .error error => panic! s!"unexpected dependency diagnostic: {error}"
  | .ok () => panic! "catalog-dependent function was accepted"
  match validateLocalConstraintDependencies "app.users" "operator_check"
      "CHECK (age OPERATOR(app.>) 0)" false true with
  | .error (.unsupportedConstraint _ _ _ diagnostic) => do
      assert! diagnostic.category == .unsupportedOperator
      assert! diagnostic.offset == 0
      assert! diagnostic.message ==
        "catalog-dependent operators are unsupported in local constraints"
  | .error error => panic! s!"unexpected dependency diagnostic: {error}"
  | .ok () => panic! "catalog-dependent operator was accepted"
  assert! (validateLocalConstraintDependencies "app.users" "builtin_check"
    "CHECK (char_length(display_name) > 0)" false false).isOk
  assert! (validateConstraintValidationMetadata "app.users" "deferred_check"
    false false).isOk
  match validateConstraintValidationMetadata "app.users" "deferred_check" false true with
  | .error (.catalog message) =>
      assert! message == "constraint app.users.deferred_check: pg_get_constraintdef validation suffix implies convalidated=true, but pg_constraint reports convalidated=false"
  | .error error => panic! s!"unexpected validation metadata diagnostic: {error}"
  | .ok () => panic! "inconsistent NOT VALID metadata was accepted"
  let normalized17 := Pg17.adapter.normalizeConstraints
    #[commonConstraint] attributeNotNull
  let normalized18 := Pg18.adapter.normalizeConstraints
    #[commonConstraint, nativeNotNull] attributeNotNull
  let constraints17 ← match normalized17 with
    | .error message => panic! message
    | .ok constraints => pure constraints
  let constraints18 ← match normalized18 with
    | .error message => panic! message
    | .ok constraints => pure constraints
  assert! constraints17 == constraints18
  let some email := constraints18.find? fun (constraint : Pgx.ConstraintIR) =>
      constraint.kind == .notNull && constraint.columns == #["email"]
    | panic! "normalized email NOT NULL constraint is missing"
  assert! email.name == "<not-null:email>"
  checkUnsafeNativeNotNullRejection
  match Pg17.adapter.normalizeConstraints
      #[commonConstraint, nativeNotNull] attributeNotNull with
  | .error _ => pure ()
  | .ok _ => panic! "PostgreSQL 17 accepted a native NOT NULL catalog row"
  match Pg18.adapter.normalizeConstraints #[nativeNotNull] #[] with
  | .error _ => pure ()
  | .ok _ => panic! "PostgreSQL 18 accepted a native NOT NULL row missing from pg_attribute"
  assert! isError (validateConfig { validConfig with schemas := #["app", "app"] })
  assert! isError (validateConfig { validConfig with schemas := #[""] })
  assert! isError (validateConfig {
    validConfig with supportedServerMajors := #[17, 18, 19]
  })
  let sparse := validConfig.queries.map fun query => {
    query with parameters := #[
      { position := 1, name := "first", nullable := false },
      { position := 3, name := "third", nullable := true }
    ]
  }
  assert! isError (validateConfig { validConfig with queries := sparse })
  let emptySql := validConfig.queries.map fun query => { query with sql := " \n\t" }
  assert! isError (validateConfig { validConfig with queries := emptySql })

  let installed := #[("vector", "0.8.0"), ("citext", "1.6")]
  let resolvedPackages ← match packageConfig.resolvedExtensionCodecPackages installed with
    | .ok value => pure value
    | .error error => panic! toString error
  assert! resolvedPackages == #[
    {
      extension := "citext"
      version := "1.6"
      importModule := "Ext.Citext"
      types := #[citextKey]
    },
    {
      extension := "vector"
      version := "0.8.0"
      importModule := "Ext.Vector"
      types := #[halfvecKey, vectorKey]
    }
  ]
  let reorderedPackages : Config := {
    packageConfig with
    requiredExtensions := packageConfig.requiredExtensions.reverse
    typeOverrides := packageConfig.typeOverrides.reverse
    extensionCodecPackages := packageConfig.extensionCodecPackages.reverse.map
      fun (package : ExtensionCodecPackageInput) =>
      { package with types := package.types.reverse }
  }
  assert! (validateConfig reorderedPackages).isOk
  match reorderedPackages.resolvedExtensionCodecPackages installed.reverse with
  | .ok value => assert! value == resolvedPackages
  | .error error => panic! toString error
  assert! isError (packageConfig.resolvedExtensionCodecPackages #[
    ("citext", "1.6")])

  let liveOverrideKeys := #[vectorKey, halfvecKey, citextKey, citextArrayKey]
  assert! (validateLiveTypeOverrides packageConfig.typeOverrides liveOverrideKeys).isOk
  assert! isError (validateLiveTypeOverrides packageConfig.typeOverrides
    #[vectorKey, citextKey, citextArrayKey])
  assert! isError (validateLiveTypeOverrides packageConfig.typeOverrides
    (liveOverrideKeys.push citextKey))

  let ownership : Array ExtensionTypeOwnership := #[
    { key := vectorKey, extension := "vector" },
    { key := halfvecKey, extension := "vector" },
    { key := citextKey, extension := "citext" },
    -- Extension-owned array wrappers are intentionally not package entries;
    -- their ordinary generated container codecs remain available.
    { key := citextArrayKey, extension := "citext" }
  ]
  assert! (validateExtensionCodecOwnership
    packageConfig.extensionCodecPackages ownership).isOk
  assert! isError (validateExtensionCodecOwnership
    packageConfig.extensionCodecPackages
    (ownership.filter fun value => value.key != citextKey))
  assert! isError (validateExtensionCodecOwnership
    packageConfig.extensionCodecPackages
    (ownership.map fun value =>
      if value.key == citextKey then { value with extension := "other" } else value))
  assert! isError (validateExtensionCodecOwnership
    packageConfig.extensionCodecPackages
    (ownership.push { key := citextKey, extension := "citext" }))
  assert! extensionTypeOwnershipSql.contains
    "dep.classid = 'pg_catalog.pg_type'::pg_catalog.regclass"
  assert! extensionTypeOwnershipSql.contains
    "dep.refclassid = 'pg_catalog.pg_extension'::pg_catalog.regclass"
  assert! extensionTypeOwnershipSql.contains "dep.objsubid = 0"
  assert! extensionTypeOwnershipSql.contains "dep.refobjsubid = 0"
  assert! extensionTypeOwnershipSql.contains "dep.deptype = 'e'"

  assert! isError (validateConfig {
    packageConfig with
    extensionCodecPackages := packageConfig.extensionCodecPackages.map
      (fun (package : ExtensionCodecPackageInput) =>
      if package.extension == "citext" then
        { package with extension := " citext" }
      else package)
  })
  assert! isError (validateConfig {
    packageConfig with
    extensionCodecPackages := packageConfig.extensionCodecPackages.map
      (fun (package : ExtensionCodecPackageInput) =>
      if package.extension == "citext" then
        { package with importModule := "" }
      else package)
  })
  assert! isError (validateConfig {
    packageConfig with
    extensionCodecPackages := packageConfig.extensionCodecPackages.map
      (fun (package : ExtensionCodecPackageInput) =>
      if package.extension == "citext" then
        { package with types := #[] }
      else package)
  })
  assert! isError (validateConfig {
    packageConfig with requiredExtensions := #["vector"]
  })
  assert! isError (validateConfig {
    packageConfig with
    extensionCodecPackages := packageConfig.extensionCodecPackages.map
      (fun (package : ExtensionCodecPackageInput) =>
      if package.extension == "citext" then
        { package with types := #[{
            schema := "public", name := "missing", kind := .base
          }] }
      else package)
  })
  assert! isError (validateConfig {
    packageConfig with
    extensionCodecPackages := packageConfig.extensionCodecPackages.map
      (fun (package : ExtensionCodecPackageInput) =>
      if package.extension == "citext" then
        { package with importModule := "Ext.Other" }
      else package)
  })
  assert! isError (validateConfig {
    packageConfig with extensionCodecPackages :=
      packageConfig.extensionCodecPackages.push {
        extension := "vector"
        importModule := "Ext.Vector"
        types := #[vectorKey]
      }
  })
  assert! isError (validateConfig {
    packageConfig with
    extensionCodecPackages := packageConfig.extensionCodecPackages.map
      (fun (package : ExtensionCodecPackageInput) =>
      if package.extension == "citext" then
        { package with types := #[vectorKey] }
      else package)
  })
  assert! isError (validateConfig {
    packageConfig with
    typeOverrides := packageConfig.typeOverrides.push
      (overrideFor { schema := " ", name := "blank", kind := .base }
        "Blank" "blankCodec" "Ext.Citext")
    extensionCodecPackages := packageConfig.extensionCodecPackages.map
      (fun (package : ExtensionCodecPackageInput) =>
      if package.extension == "citext" then
        { package with types := #[{ schema := " ", name := "blank", kind := .base }] }
      else package)
  })

  assert! analyzeOuterJoinPlanJson innerPlan == .noOuterJoin
  assert! analyzeOuterJoinPlanJson leftPlan == .outerJoin
  assert! analyzeOuterJoinPlanJson fullPlan == .outerJoin
  let single := analyzeQueryPlanJson singleRelationPlan
  assert! single.outerJoins == .noOuterJoin
  assert! single.rowPreservedRelations == #[relation]
  let selfJoin := analyzeQueryPlanJson selfJoinPlan
  assert! selfJoin.outerJoins == .noOuterJoin
  assert! selfJoin.rowPreservedRelations.isEmpty
  let twoRelations := analyzeQueryPlanJson twoRelationPlan
  assert! twoRelations.outerJoins == .noOuterJoin
  assert! twoRelations.rowPreservedRelations == #[relation,
    { schema := "app", name := "profiles" }]
  assert! (analyzeQueryPlanJson leftPlan).rowPreservedRelations.isEmpty
  assert! analyzeOuterJoinPlanJson
    "[{\"Plan\":{\"Node Type\":\"Future Scan\"}}]" == .uncertain
  assert! analyzeOuterJoinPlanJson
    "{\"unexpected\":{\"Node Type\":\"Seq Scan\"}}" == .uncertain
  assert! analyzeOuterJoinPlanJson
    "[{\"Plan\":{\"Node Type\":\"Seq Scan\"}" == .uncertain
  return 0

end Pgx.Test.Probe

def main : IO UInt32 := Pgx.Test.Probe.main
