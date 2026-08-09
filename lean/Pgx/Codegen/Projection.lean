import Pgx.IR

/-!
# Direct-projection refinement planning

This pass propagates a table-local check into a query result only when the
query descriptor proves a complete, unambiguous identity projection of every
source column used by the check.  Result names and SQL types alone are never
treated as provenance.
-/

namespace Pgx.Codegen.Projection

open Pgx.Constraint

private def exactlyOne? (values : Array α) : Option α :=
  if values.size == 1 then values[0]? else none

private def sourceRelation? (relations : Array Pgx.RelationIR)
    (key : Pgx.RelationKey) : Option Pgx.RelationIR :=
  exactlyOne? (relations.filter fun relation => relation.key == key)

private def sourceColumn? (relation : Pgx.RelationIR)
    (name : String) : Option Pgx.RelationColumnIR :=
  exactlyOne? (relation.columns.filter fun column => column.name == name)

private def resultColumn? (query : Pgx.QueryIR) (key : Pgx.ColumnKey) :
    Option Pgx.QueryColumnIR :=
  exactlyOne? (query.columns.filter fun column => column.origin == some key)

/-- Resolve one source column to one descriptor-proven result projection.
`logicalType` separates a domain's refined logical type from its base wire
type.  Widening a known non-null source to a nullable result is rejected. -/
private def directProjection? (relation : Pgx.RelationIR) (query : Pgx.QueryIR)
    (sourceName : String) : Option (Pgx.RelationColumnIR × Pgx.QueryColumnIR) := do
  let source ← sourceColumn? relation sourceName
  let result ← resultColumn? query { relation := relation.key, name := sourceName }
  guard (result.logicalType.getD result.ty == source.ty)
  -- A synthetic outer-join null does not establish that a source row exists.
  guard (!result.nullWidened)
  guard (!result.nullable || source.nullable)
  pure (source, result)

private def queryProjectsRelation (relation : Pgx.RelationIR)
    (query : Pgx.QueryIR) : Bool :=
  relation.columns.any fun source =>
    (directProjection? relation query source.name).isSome

private def rewriteValue? (relation : Pgx.RelationIR) (query : Pgx.QueryIR) :
    ValueExpr → Option ValueExpr
  | .column sourceName ty _ => do
      let (source, result) ← directProjection? relation query sourceName
      guard (ty.declared == source.ty)
      pure (.column result.name ty result.nullable)
  | .domainValue ty nullable => some (.domainValue ty nullable)
  | .literal value ty => some (.literal value ty)
  | .cast preservation value target => do
      pure (.cast preservation (← rewriteValue? relation query value) target)
  | .neg value result => do
      pure (.neg (← rewriteValue? relation query value) result)
  | .add left right result => do
      pure (.add (← rewriteValue? relation query left)
        (← rewriteValue? relation query right) result)
  | .sub left right result => do
      pure (.sub (← rewriteValue? relation query left)
        (← rewriteValue? relation query right) result)
  | .charLength value result => do
      pure (.charLength (← rewriteValue? relation query value) result)
  | .btrim value result => do
      pure (.btrim (← rewriteValue? relation query value) result)
  | .position substring string result => do
      pure (.position (← rewriteValue? relation query substring)
        (← rewriteValue? relation query string) result)

private def rewriteTruth? (relation : Pgx.RelationIR) (query : Pgx.QueryIR) :
    TruthExpr → Option TruthExpr
  | .constant value => some (.constant value)
  | .fromBoolean value => do
      pure (.fromBoolean (← rewriteValue? relation query value))
  | .compare operator left right => do
      pure (.compare operator (← rewriteValue? relation query left)
        (← rewriteValue? relation query right))
  | .isNull value => do
      pure (.isNull (← rewriteValue? relation query value))
  | .isNotNull value => do
      pure (.isNotNull (← rewriteValue? relation query value))
  | .and left right => do
      pure (.and (← rewriteTruth? relation query left)
        (← rewriteTruth? relation query right))
  | .or left right => do
      pure (.or (← rewriteTruth? relation query left)
        (← rewriteTruth? relation query right))
  | .not value => do
      pure (.not (← rewriteTruth? relation query value))

private def projectConstraint? (relations : Array Pgx.RelationIR)
    (query : Pgx.QueryIR) (constraint : Pgx.ConstraintIR) :
    Option Pgx.QueryConstraintIR := do
  guard (constraint.kind == .check)
  let expression ← constraint.localExpression
  let relation ← sourceRelation? relations constraint.relation
  -- RowDescription identifies only the base relation and attribute.  The
  -- plan-level witness rules out mixing columns from different self-join
  -- aliases and rules out synthetic outer-join rows.
  guard (query.rowPreservedRelations.contains relation.key)
  -- A constant check still needs descriptor provenance tying this query to
  -- the relation; otherwise the vacuous column traversal would attach every
  -- constant check in the database to every query.
  guard (queryProjectsRelation relation query)
  let rewritten ← rewriteTruth? relation query expression
  pure {
    relation := relation.key
    name := constraint.name
    source := constraint.expression.getD ""
    expression := rewritten
    validated := constraint.validated
  }

/-- Compute the complete local-refinement contract for one query. -/
def localConstraints (relations : Array Pgx.RelationIR)
    (constraints : Array Pgx.ConstraintIR) (query : Pgx.QueryIR) :
    Array Pgx.QueryConstraintIR :=
  constraints.filterMap (projectConstraint? relations query)

/-- Replace any previous projection plan with a plan derived solely from the
current canonical relation, constraint, and query descriptors. -/
def planQuery (relations : Array Pgx.RelationIR)
    (constraints : Array Pgx.ConstraintIR) (query : Pgx.QueryIR) : Pgx.QueryIR :=
  { query with localConstraints := localConstraints relations constraints query }

/-- Plan direct-projection refinements for every query in a database IR. -/
def planDatabase (database : Pgx.DatabaseIR) : Pgx.DatabaseIR :=
  { database with queries := database.queries.map (fun query =>
      planQuery database.relations database.constraints query) }

end Pgx.Codegen.Projection
