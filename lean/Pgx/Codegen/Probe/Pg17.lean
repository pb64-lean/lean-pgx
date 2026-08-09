import Pgx.Codegen.Probe.Adapter

namespace Pgx.Codegen.Probe.Pg17

/-- PostgreSQL 17 obtains relation `NOT NULL` constraints from
`pg_attribute.attnotnull`. -/
def adapter : Adapter := {
  serverMajor := 17
  notNullCatalog := .attributeOnly
}

end Pgx.Codegen.Probe.Pg17
