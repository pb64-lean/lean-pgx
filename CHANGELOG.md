# Changelog

All notable changes will be documented in this file. The project has not yet
made a stable release; the `0.1.0` Bazel module version is a development
coordinate.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added

- Bazel rules for server-authoritative generation, live acceptance tests, and
  PostgreSQL 17/18 compatibility checks.
- Canonical symbolic schema/query IR, contract fingerprints, and generated
  Lean modules for types, schema metadata, constraints, and queries.
- Runtime checked attachment, symbolic OID resolution, descriptor verification,
  cardinality enforcement, and typed drift/codec/constraint errors.
- Generated codecs and local refinements for built-in types, enums, domains,
  one-dimensional arrays, named composites, ranges, and multiranges.
- Extension codec packages and direct type overrides.
- Proof-producing validation for the supported normalized `CHECK` subset and
  safe propagation through verified direct query projections.
- A finite duplicate-preserving relational state model, propositions for the
  supported relational constraints, and abstract one-occurrence mutation
  specifications.
- Public setup, architecture, support, trust, rule, manifest, generated API,
  runtime error, design, contribution, security, conduct, and roadmap docs.
- An exact assurance policy for the public `Pgx` module surface, including
  pinned principal theorem statements and trust-boundary inventories.
