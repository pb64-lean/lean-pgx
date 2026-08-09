import Pgx.Codegen.Probe.Adapter

namespace Pgx.Codegen.Probe.Pg18

/-- PostgreSQL 18 exposes native relation `NOT NULL` rows in `pg_constraint`;
the shared adapter boundary canonicalizes them before emission. -/
def adapter : Adapter := {
  serverMajor := 18
  notNullCatalog := .nativeConstraint
}

end Pgx.Codegen.Probe.Pg18
