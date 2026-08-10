# Security policy

## Supported versions

`lean-pgx` is pre-release. Only the current main development line receives
security fixes; no released version currently carries a stable support
commitment.

## Reporting a vulnerability

Please do not open a public issue for a suspected vulnerability. Use GitHub's
private vulnerability reporting flow from this repository's **Security** tab.
If that flow is unavailable, contact the repository maintainers privately
through the `pb64-lean` organization before disclosing details publicly.

Include, when possible:

- the affected revision and environment;
- a minimal reproduction or proof of concept;
- the expected and observed trust-boundary behavior;
- potential impact; and
- any known mitigation.

The maintainers do not currently promise a response SLA. They will coordinate
validation, remediation, and disclosure through the private report.

## Relevant security boundary

The generated Lean proof layer does not establish that a live PostgreSQL
server is faithful to the pure logical model. PostgreSQL, `pg-lean`, catalog
and protocol observations, code generation, and runtime I/O are within the
trusted computing boundary. See
[`docs/assurance-and-trust.md`](docs/assurance-and-trust.md) before evaluating
the impact of a mismatch.
