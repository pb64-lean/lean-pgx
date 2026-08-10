# Contributing to lean-pgx

Thank you for helping improve `lean-pgx`. The project is pre-release, so a
change may refine both implementation and public API, but compatibility and
migration consequences should be made explicit.

Participation is governed by the [Code of Conduct](CODE_OF_CONDUCT.md).
Security-sensitive reports belong in the private channel described in
[SECURITY.md](SECURITY.md), not a public issue.

## Development setup

Use sibling checkouts with this layout:

```text
workspace/
├── lean-pgx/
├── pg-lean/
├── rules_lean/
└── tls13-lean/
```

Use a Linux or macOS POSIX host with Bazel directory runfiles enabled. Install
Bazel or Bazelisk, Nix, Bash, and the editor toolchain named by
[`lean-toolchain`](lean-toolchain). The root `MODULE.bazel` contains local
development overrides and registers the Nix-backed Lean toolchain.

Run the authoritative checks from the repository root:

```sh
bazel build //...
bazel test //...
```

Changes to Bazel rules, module extensions, repository labels, or public build
APIs must also pass the separately rooted dependency-mode fixture (it is
excluded from the parent workspace by `.bazelignore`):

```sh
(cd integration/downstream && bazel test //... --lockfile_mode=error)
```

The committed module lockfile is read-only during ordinary commands. After an
intentional `MODULE.bazel` or extension dependency change, refresh it explicitly
and review the resulting diff:

```sh
bazel mod graph --lockfile_mode=update
```

`lake build` is useful for editor feedback, but a passing Lake build does not
replace Bazel validation. Bazel owns code generation, transient PostgreSQL
lifecycle, compatibility fixtures, and the release-shaped dependency graph.

## Change guidelines

- Add focused tests for parser, IR, generator, runtime, or proof changes.
- Add or extend a live fixture when behavior depends on real PostgreSQL
  catalogs, statement descriptors, DDL, or wire values.
- Do not hand-edit generated Lean or `.pgir.json` outputs; change the probe,
  IR, or emitter and regenerate them through Bazel.
- Keep symbolic catalog identities free of installation-local OIDs.
- Reject unsupported semantics explicitly instead of silently weakening a
  generated type or proposition.
- Update the support matrix, reference docs, and changelog when a public
  contract changes.
- Keep code-generation actions hermetic: all migrations, queries, executables,
  and lifecycle tools must be declared inputs.

Prefer small commits that leave the build green. A pull request should explain
the contract being changed, the PostgreSQL versions exercised, and which
tests establish the new behavior.

## Documentation

Public Bazel attributes belong in
[`docs/reference/bazel-rules.md`](docs/reference/bazel-rules.md), manifest
changes in [`docs/reference/manifest.md`](docs/reference/manifest.md), and
support limitations in [`docs/support.md`](docs/support.md). Record durable,
cross-cutting architecture choices as a short design decision in
[`docs/design/`](docs/design/).

## Licensing

By contributing, you agree that your contributions are licensed under the
[Apache License 2.0](LICENSE).
