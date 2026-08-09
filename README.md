# lean-pgx

Lean 4 PostgreSQL extensions built on [`pg-lean`](../pg-lean).

## Build

The authoritative build uses Bazel and expects `rules_lean`, `pg-lean`, and
`tls13-lean` as sibling checkouts. Build the primary library target with:

```sh
bazel build //lean:pgx
```

Build every target in the workspace with:

```sh
bazel build //...
```

## Editor support

Lake supplies the editor project model and resolves `pg-lean` from its sibling
checkout. Bazel remains the authoritative build system.

```sh
lake update
lake serve
```
