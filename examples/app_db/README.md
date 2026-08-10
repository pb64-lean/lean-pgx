# AppDb conformance fixture

This directory is lean-pgx's exhaustive end-to-end fixture, not its introductory
example. It covers the supported schema and query surface, PostgreSQL 17/18
compatibility, generated proof-bearing values, relational specifications,
extension codecs, live attachment, descriptor drift, and runtime failures.

For a compact starting point, see `../quickstart`.

Run the complete fixture with:

```sh
bazel test //examples/app_db:all
```
