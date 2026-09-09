import Pgx.Typed.Query

/-!
PGX-13's exact selected-once row dispatcher, isolated in its own compilation
unit so the differential benchmark enters both old and staged dispatchers
through equivalent exported no-inline wrappers.
-/

namespace Pgx.Typed.PreparedRowDispatchBenchmarkEager

@[noinline] private def decodeEagerCandidateCore
    (spec : QuerySpec db Params Row .many) (plan : PreparedQueryPlan db)
    (catalog : ResolvedCatalog db) (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  let expectedColumns := spec.columns.size
  match spec.preparedSpanDecoderBundle with
  | some bundle =>
    if bundle.expectedColumns = expectedColumns then
      bundle.many plan.resolve plan.results columns rows
    else
      guardedPreparedSpanRows expectedColumns bundle.row
        plan.resolve plan.results columns rows
  | none =>
    match spec.preparedSpanDecode with
    | some decode =>
      guardedPreparedSpanRows expectedColumns decode
        plan.resolve plan.results columns rows
    | none =>
      match spec.preparedDecode with
      | some decode =>
        rows.mapM fun values =>
          if values.size = expectedColumns then
            let materialized := values.materialize
            decode plan.resolve plan.results columns materialized
          else
            throw (dataRowArityError values.size expectedColumns)
      | none =>
        let decode := spec.decode
        rows.mapM fun values =>
          if values.size = expectedColumns then
            let materialized := values.materialize
            decode catalog columns materialized
          else
            throw (dataRowArityError values.size expectedColumns)

/-- Exported benchmark entry matching the production candidate harness shape. -/
@[noinline] def decodeEagerCandidate
    (spec : QuerySpec db Params Row .many) (plan : PreparedQueryPlan db)
    (catalog : ResolvedCatalog db) (columns : Array Pg.Protocol.ColumnDesc)
    (rows : Array Pg.Protocol.DataRowSpans) : Except Error (Array Row) :=
  decodeEagerCandidateCore spec plan catalog columns rows

end Pgx.Typed.PreparedRowDispatchBenchmarkEager
