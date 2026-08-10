# Quickstart example

This is the smallest complete lean-pgx application in the repository. It:

1. replays one migration into a fresh PostgreSQL instance;
2. generates `QuickstartDb` from one literal query;
3. attaches a raw pg-lean connection to the generated contract; and
4. executes and decodes the checked query.

Run it with:

```sh
bazel test //examples/quickstart:runtime_test
```

The exhaustive compatibility and drift fixture lives in `examples/app_db`.
