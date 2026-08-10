# Runtime errors

Generated attachment and query runners return `Except Pgx.Typed.Error α` inside
`Std.Async.Async`. Handle the error explicitly or convert it at one application
boundary with context:

```lean
private def typed! (context : String) (result : Except Pgx.Typed.Error α) :
    Std.Async.Async α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")
```

`ToString Pgx.Typed.Error` adds the category prefix shown below. For
programmatic handling, use `error.kind` rather than parsing that text.
`error.postgres?`, `error.driftContext?`, and
`error.cardinalityContext?` recover structured payloads for the corresponding
categories.

## Error categories

| Constructor | Message prefix | Meaning and typical response |
| --- | --- | --- |
| `postgres Pg.Error` | PostgreSQL/transport message | The server, connection, or protocol operation failed. Classify the wrapped `Pg.Error`; retry only according to normal database policy. |
| `schemaDrift String` | `schema drift:` | A live symbolic schema descriptor, session fact, extension package, or codec expectation differs from generated code. Stop using the capability, compare migrations/deployment with the generated artifact, and regenerate or migrate. |
| `queryDrift String` | `query drift:` | A successfully prepared statement or returned result descriptor differs, or a cached plan changed its result type. Do not decode the result. Reconcile SQL/schema and recreate the connection after correction. |
| `unsupportedType TypeKey` | `unsupported PostgreSQL type:` | Runtime resolution reached a type without a supported built-in or declared codec. Add an exact override or remove that type from the contract. |
| `constraintViolation ConstraintViolation` | `local constraint violation:` | A generated local domain, row, or type-modifier predicate rejected data during validation/decoding. Treat stored-data failures as schema/data integrity incidents; do not manufacture the proof-bearing value. |
| `encode String` | `parameter encoding failed:` | A generated or custom parameter codec rejected the value, returned the wrong shape/format, or failed conversion. Validate application input and custom codecs. |
| `decode String` | `row decoding failed:` | Bytes, text, nullability, container shape, or a custom codec did not match the expected Lean value. Treat this as data drift, unsupported wire behavior, or a codec defect. |
| `cardinality expected actual` | `cardinality mismatch:` | Actual row count violates `exactlyOne` or `zeroOrOne`. Correct the query/data invariant or change the manifest contract. |

## Attachment errors

`AppDb.attach raw` can return PostgreSQL, schema drift, unsupported type, and
other descriptor/codec errors. It does not partially return a checked
capability. Log enough context to identify the generated contract and server,
but do not include credentials from the connection URL.

If attachment fails because deployment is between migrations and application
rollout, keep that instance out of service until the schema and generated code
match. Repeatedly retrying an invariant mismatch does not make the connection
safe.

## Query drift and prepared cache state

Preparation is lazy and shared by calls on one checked connection. A verified
statement is reused. Descriptor drift for an already-created generated
statement remains sticky in that connection's cache; transient failures before
a usable preparation may be retried by a later call.

Recreate the raw connection after correcting drift. Do not use
`CheckedConnection.raw` to deallocate or replace generated statement names.

## Constraint violations

`Pgx.ConstraintViolation` identifies the generated local obligation that
failed, such as a named check or type-modifier validation. It is separate from
a PostgreSQL server constraint error:

- a server rejection arrives as `.postgres (.server ...)`; and
- a Lean-side revalidation failure arrives as `.constraintViolation ...`.

This distinction matters when diagnosing rows inserted through other clients,
disabled/unvalidated database constraints, or custom codec behavior.

## Cardinality is an application contract

PostgreSQL statement description does not prove result count. `lean-pgx`
buffers the result and enforces the manifest declaration:

- `exactlyOne` rejects zero and more than one row;
- `zeroOrOne` rejects more than one row;
- `many` accepts any count; and
- `execute` rejects returned data rows but does not promise a particular
  affected-row count.

If uniqueness is intended to justify `zeroOrOne`, keep the supporting schema
constraint in the generated contract and still handle cardinality errors as a
defensive runtime failure.
