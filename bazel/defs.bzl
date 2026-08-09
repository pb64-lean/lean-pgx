"""Bazel rules for checked PostgreSQL schema and query generation.

The generation rule owns an empty PostgreSQL cluster, replays only declared
migration inputs, and probes literal query files.  Nothing in the ordinary
build connects to a developer or production database.
"""

load("@rules_lean//lean:defs.bzl", "lean_library")

PgQuerySetInfo = provider(
    doc = "Literal SQL query inputs and their declarative manifest.",
    fields = {
        "srcs": "Ordered query source files.",
        "manifest": "The query manifest file.",
        "lean_names": "Declared output module names derived from filenames.",
    },
)

LeanPgGenInfo = provider(
    doc = "Generated Lean PostgreSQL contract sources and replay metadata.",
    fields = {
        "lean_srcs": "Generated Lean source files.",
        "schema_ir": "Canonical symbolic schema/query IR snapshot.",
        "contract_hash": "Canonical-major semantic contract fingerprint.",
        "compatibility_hash": "Major-independent contract fingerprint.",
        "module_prefix": "Root Lean module name.",
        "query_names": "Generated query module names.",
        "migrations": "Ordered DDL migration files.",
        "query_srcs": "Ordered literal query files.",
        "manifest": "Query manifest file.",
        "schemas": "Schemas included in the generated contract.",
        "server_majors": "PostgreSQL majors accepted by CheckedConnection.",
    },
)

_PgCompatSnapshotInfo = provider(
    fields = {
        "schema_ir": "Canonical snapshot produced by one PostgreSQL major.",
        "major": "PostgreSQL major used for this snapshot.",
    },
)

def _pascal_case(value):
    result = []
    capitalize = True
    alphanumeric = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    for i in range(len(value)):
        char = value[i]
        if char in alphanumeric:
            result.append(char.upper() if capitalize else char)
            capitalize = False
        else:
            capitalize = True
    return "".join(result)

def _query_lean_name(src):
    if not src.basename.endswith(".sql"):
        fail("pg_query_set sources must end in .sql: %s" % src.path)
    stem = src.basename[:-len(".sql")]
    result = _pascal_case(stem)
    if not result:
        fail("query filename does not produce a Lean module name: %s" % src.path)
    if result[0] in "0123456789":
        fail("query filename produces a Lean module beginning with a digit: %s" % src.path)
    return result

def _pg_query_set_impl(ctx):
    names = []
    seen = {}
    for src in ctx.files.srcs:
        name = _query_lean_name(src)
        if name in seen:
            fail("query filenames produce duplicate Lean module %s: %s and %s" % (
                name,
                seen[name].path,
                src.path,
            ))
        seen[name] = src
        names.append(name)
    if not ctx.files.srcs:
        fail("pg_query_set requires at least one literal .sql source")
    return [
        DefaultInfo(files = depset(ctx.files.srcs + [ctx.file.manifest])),
        PgQuerySetInfo(
            srcs = ctx.files.srcs,
            manifest = ctx.file.manifest,
            lean_names = names,
        ),
    ]

_pg_query_set = rule(
    implementation = _pg_query_set_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".sql"],
            mandatory = True,
        ),
        "manifest": attr.label(
            allow_single_file = [".json"],
            mandatory = True,
        ),
    },
)

def pg_query_set(name, srcs, manifest, visibility = None, **kwargs):
    """Collects one-statement SQL files and their query manifest."""
    _pg_query_set(
        name = name,
        srcs = srcs,
        manifest = manifest,
        visibility = visibility,
        **kwargs
    )

def _module_path(module_prefix):
    if not module_prefix:
        fail("module_prefix must not be empty")
    return module_prefix.replace(".", "/")

def _find_distribution_tool(files, basename, distribution):
    matches = [f for f in files if f.basename == basename and f.dirname.endswith("/bin")]
    if len(matches) != 1:
        fail("%s distribution must contain exactly one bin/%s (found %s)" % (
            distribution,
            basename,
            len(matches),
        ))
    return matches[0]

def _find_postgres_tool(files, basename):
    return _find_distribution_tool(files, basename, "PostgreSQL")

def _add_common_generator_args(args, ctx, query_info):
    args.add("--module-prefix")
    args.add(ctx.attr.module_prefix)
    args.add("--canonical-major")
    args.add(ctx.attr.canonical_major)
    args.add("--manifest")
    args.add(query_info.manifest)
    for major in ctx.attr.server_majors:
        args.add("--server-major")
        args.add(major)
    for schema in ctx.attr.schemas:
        args.add("--schema")
        args.add(schema)
    for migration in ctx.files.migrations:
        args.add("--migration")
        args.add(migration)
    for i in range(len(query_info.srcs)):
        args.add("--query-name")
        args.add(query_info.lean_names[i])
        args.add("--query-file")
        args.add(query_info.srcs[i])

_SERVER_LIFECYCLE = r"""set -euo pipefail
export LC_ALL=C
export TZ=UTC
pgx_absolute() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *) printf '%s/%s\n' "$PWD" "$1" ;;
  esac
}
INITDB="$(pgx_absolute "$1")"
POSTGRES="$(pgx_absolute "$2")"
PG_ISREADY="$(pgx_absolute "$3")"
PG_CTL="$(pgx_absolute "$4")"
SOCAT="$(pgx_absolute "$5")"
MKTEMP="$(pgx_absolute "$6")"
MKDIR="$(pgx_absolute "$7")"
RM="$(pgx_absolute "$8")"
SLEEP="$(pgx_absolute "$9")"
GENERATOR="$(pgx_absolute "${10}")"
shift 10

pgx_print_log() {
  PGX_PRINT_FILE="$1"
  PGX_PRINT_COUNT=0
  while [ "$PGX_PRINT_COUNT" -lt 240 ] && IFS= read -r PGX_PRINT_LINE; do
    printf '%s\n' "$PGX_PRINT_LINE" >&2
    PGX_PRINT_COUNT=$((PGX_PRINT_COUNT + 1))
  done < "$PGX_PRINT_FILE"
}

PGX_TMP_ROOT="$(pgx_absolute "${TEST_TMPDIR:-${TMPDIR:-/tmp}}")"
PGX_WORK="$("$MKTEMP" -d "$PGX_TMP_ROOT/lean-pgx.XXXXXX")"
case "$PGX_WORK" in
  "$PGX_TMP_ROOT"/lean-pgx.*) ;;
  *) echo "refusing unexpected temporary path: $PGX_WORK" >&2; exit 1 ;;
esac
PGX_DATA="$PGX_WORK/data"
PGX_SOCKET="$PGX_WORK/socket"
PGX_LOG="$PGX_WORK/postgres.log"
PGX_SOCAT_LOG="$PGX_WORK/socat.log"
PGX_POSTGRES_PID=""
PGX_SOCAT_PID=""

cleanup() {
  PGX_STATUS=$?
  trap - EXIT INT TERM
  if [ -n "$PGX_SOCAT_PID" ]; then
    if kill -0 "$PGX_SOCAT_PID" 2>/dev/null; then
      kill "$PGX_SOCAT_PID" 2>/dev/null || true
    fi
    wait "$PGX_SOCAT_PID" 2>/dev/null || true
  fi
  if [ -n "$PGX_POSTGRES_PID" ]; then
    if kill -0 "$PGX_POSTGRES_PID" 2>/dev/null; then
      if ! "$PG_CTL" -D "$PGX_DATA" -m fast -w stop >/dev/null 2>&1; then
        kill "$PGX_POSTGRES_PID" 2>/dev/null || true
      fi
    fi
    wait "$PGX_POSTGRES_PID" 2>/dev/null || true
  fi
  if [ "$PGX_STATUS" -ne 0 ] && [ -f "$PGX_LOG" ]; then
    echo "PostgreSQL action log:" >&2
    pgx_print_log "$PGX_LOG"
  fi
  if [ "$PGX_STATUS" -ne 0 ] && [ -s "$PGX_SOCAT_LOG" ]; then
    echo "socat action log:" >&2
    pgx_print_log "$PGX_SOCAT_LOG"
  fi
  case "$PGX_WORK" in
    "$PGX_TMP_ROOT"/lean-pgx.*) "$RM" -rf -- "$PGX_WORK" ;;
  esac
  exit "$PGX_STATUS"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$MKDIR" -p "$PGX_SOCKET"

TZ=UTC "$INITDB" -D "$PGX_DATA" --no-locale --encoding=UTF8 \
  --auth=trust --username=postgres >"$PGX_LOG" 2>&1

PGX_DB_PORT=5432
TZ=UTC "$POSTGRES" -D "$PGX_DATA" \
  -c listen_addresses= -c unix_socket_directories="$PGX_SOCKET" \
  -p "$PGX_DB_PORT" -c timezone=UTC -c max_connections=16 \
  >>"$PGX_LOG" 2>&1 &
PGX_POSTGRES_PID=$!

PGX_DB_READY=""
PGX_ATTEMPT=0
while [ "$PGX_ATTEMPT" -lt 600 ]; do
  if ! kill -0 "$PGX_POSTGRES_PID" 2>/dev/null; then
    break
  fi
  if "$PG_ISREADY" -q -h "$PGX_SOCKET" -p "$PGX_DB_PORT" -U postgres; then
    PGX_DB_READY=1
    break
  fi
  PGX_ATTEMPT=$((PGX_ATTEMPT + 1))
  "$SLEEP" 0.05
done

if [ -z "$PGX_DB_READY" ]; then
  echo "PostgreSQL failed to start on its private Unix socket" >&2
  pgx_print_log "$PGX_LOG"
  exit 1
fi

PGX_BRIDGE_READY=""
PGX_ATTEMPT=0
while [ "$PGX_ATTEMPT" -lt 25 ]; do
  PGX_PORT=$((20000 + (($$ * 1103 + PGX_ATTEMPT * 997 + RANDOM) % 30000)))
  "$SOCAT" \
    "TCP4-LISTEN:$PGX_PORT,bind=127.0.0.1,reuseaddr,nodelay,fork" \
    "UNIX-CONNECT:$PGX_SOCKET/.s.PGSQL.$PGX_DB_PORT" \
    >>"$PGX_SOCAT_LOG" 2>&1 &
  PGX_SOCAT_PID=$!
  "$SLEEP" 0.05
  PGX_READY_ATTEMPT=0
  while [ "$PGX_READY_ATTEMPT" -lt 200 ]; do
    if ! kill -0 "$PGX_SOCAT_PID" 2>/dev/null; then
      break
    fi
    if "$PG_ISREADY" -q -h 127.0.0.1 -p "$PGX_PORT" -U postgres; then
      PGX_BRIDGE_READY=1
      break
    fi
    PGX_READY_ATTEMPT=$((PGX_READY_ATTEMPT + 1))
    "$SLEEP" 0.05
  done
  if [ -n "$PGX_BRIDGE_READY" ]; then
    break
  fi
  if kill -0 "$PGX_SOCAT_PID" 2>/dev/null; then
    kill "$PGX_SOCAT_PID" 2>/dev/null || true
  fi
  wait "$PGX_SOCAT_PID" 2>/dev/null || true
  PGX_SOCAT_PID=""
  PGX_ATTEMPT=$((PGX_ATTEMPT + 1))
done

if [ -z "$PGX_BRIDGE_READY" ]; then
  echo "socat failed to bridge loopback TCP to the private PostgreSQL socket" >&2
  if [ -s "$PGX_SOCAT_LOG" ]; then
    pgx_print_log "$PGX_SOCAT_LOG"
  fi
  exit 1
fi

PGX_URL="postgres://postgres@127.0.0.1:$PGX_PORT/postgres?sslmode=disable"
"$GENERATOR" --url "$PGX_URL" "$@"
"""

def _lean_pg_generate_impl(ctx):
    query_info = ctx.attr.queries[PgQuerySetInfo]
    module_path = _module_path(ctx.attr.module_prefix)

    types_out = ctx.actions.declare_file(module_path + "/Types.lean")
    schema_out = ctx.actions.declare_file(module_path + "/Schema.lean")
    constraints_out = ctx.actions.declare_file(module_path + "/Constraints.lean")
    query_outs = [
        ctx.actions.declare_file(module_path + "/Queries/" + name + ".lean")
        for name in query_info.lean_names
    ]
    root_out = ctx.actions.declare_file(module_path + ".lean")
    ir_out = ctx.actions.declare_file(ctx.attr.output_basename + ".pgir.json")
    contract_out = ctx.actions.declare_file(
        ctx.attr.output_basename + ".contract.sha256",
    )
    compatibility_out = ctx.actions.declare_file(
        ctx.attr.output_basename + ".compatibility.sha256",
    )
    lean_srcs = [types_out, schema_out, constraints_out] + query_outs + [root_out]
    outputs = lean_srcs + [ir_out, contract_out, compatibility_out]

    args = ctx.actions.args()
    _add_common_generator_args(args, ctx, query_info)
    args.add("--types-out")
    args.add(types_out)
    args.add("--schema-out")
    args.add(schema_out)
    args.add("--constraints-out")
    args.add(constraints_out)
    args.add("--root-out")
    args.add(root_out)
    args.add("--ir-out")
    args.add(ir_out)
    args.add("--contract-out")
    args.add(contract_out)
    args.add("--compatibility-out")
    args.add(compatibility_out)
    for i in range(len(query_outs)):
        args.add("--query-out")
        args.add(query_info.lean_names[i] + "=" + query_outs[i].path)

    postgres_files = ctx.files.postgres
    initdb = _find_postgres_tool(postgres_files, "initdb")
    postgres = _find_postgres_tool(postgres_files, "postgres")
    pg_isready = _find_postgres_tool(postgres_files, "pg_isready")
    pg_ctl = _find_postgres_tool(postgres_files, "pg_ctl")
    socat_files = ctx.files._socat
    socat = _find_distribution_tool(socat_files, "socat", "socat")
    coreutils_files = ctx.files._coreutils
    mktemp = _find_distribution_tool(coreutils_files, "mktemp", "coreutils")
    mkdir = _find_distribution_tool(coreutils_files, "mkdir", "coreutils")
    rm = _find_distribution_tool(coreutils_files, "rm", "coreutils")
    sleep = _find_distribution_tool(coreutils_files, "sleep", "coreutils")

    ctx.actions.run_shell(
        command = _SERVER_LIFECYCLE,
        arguments = [
            initdb.path,
            postgres.path,
            pg_isready.path,
            pg_ctl.path,
            socat.path,
            mktemp.path,
            mkdir.path,
            rm.path,
            sleep.path,
            ctx.executable._generator.path,
            args,
        ],
        inputs = depset(
            direct = ctx.files.migrations + query_info.srcs + [query_info.manifest],
        ),
        outputs = outputs,
        tools = depset(
            direct = postgres_files + socat_files + coreutils_files + [ctx.executable._generator],
        ),
        use_default_shell_env = False,
        execution_requirements = {
            "block-network": "1",
        },
        mnemonic = "LeanPgGenerate",
        progress_message = "Replaying DDL and generating checked Lean API for %s" % ctx.label,
    )

    return [
        DefaultInfo(files = depset(outputs)),
        OutputGroupInfo(
            lean_srcs = depset(lean_srcs),
            schema_ir = depset([ir_out]),
            contract_hash = depset([contract_out]),
            compatibility_hash = depset([compatibility_out]),
        ),
        LeanPgGenInfo(
            lean_srcs = depset(lean_srcs),
            schema_ir = ir_out,
            contract_hash = contract_out,
            compatibility_hash = compatibility_out,
            module_prefix = ctx.attr.module_prefix,
            query_names = query_info.lean_names,
            migrations = ctx.files.migrations,
            query_srcs = query_info.srcs,
            manifest = query_info.manifest,
            schemas = ctx.attr.schemas,
            server_majors = ctx.attr.server_majors,
        ),
    ]

_lean_pg_generate = rule(
    implementation = _lean_pg_generate_impl,
    attrs = {
        "module_prefix": attr.string(mandatory = True),
        "output_basename": attr.string(mandatory = True),
        "migrations": attr.label_list(
            allow_files = [".sql"],
            mandatory = True,
        ),
        "queries": attr.label(
            mandatory = True,
            providers = [PgQuerySetInfo],
        ),
        "schemas": attr.string_list(mandatory = True),
        "postgres": attr.label(
            default = "@postgresql_18//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
        "canonical_major": attr.int(default = 18),
        "server_majors": attr.int_list(default = [17, 18]),
        "_generator": attr.label(
            default = "@lean-pgx//lean/Pgx/Codegen:pgx_codegen",
            executable = True,
            cfg = "exec",
        ),
        "_socat": attr.label(
            default = "@socat//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
        "_coreutils": attr.label(
            default = "@coreutils//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
    },
)

def _pg_compat_snapshot_impl(ctx):
    database = ctx.attr.database[LeanPgGenInfo]
    ir_out = ctx.actions.declare_file(ctx.label.name + ".pgir.json")
    contract_out = ctx.actions.declare_file(ctx.label.name + ".contract.sha256")
    compatibility_out = ctx.actions.declare_file(
        ctx.label.name + ".compatibility.sha256",
    )

    args = ctx.actions.args()
    args.add("--probe-only")
    args.add("--module-prefix")
    args.add(database.module_prefix)
    args.add("--canonical-major")
    args.add(ctx.attr.major)
    args.add("--manifest")
    args.add(database.manifest)
    for major in database.server_majors:
        args.add("--server-major")
        args.add(major)
    for schema in database.schemas:
        args.add("--schema")
        args.add(schema)
    for migration in database.migrations:
        args.add("--migration")
        args.add(migration)
    for i in range(len(database.query_srcs)):
        args.add("--query-name")
        args.add(database.query_names[i])
        args.add("--query-file")
        args.add(database.query_srcs[i])
    args.add("--ir-out")
    args.add(ir_out)
    args.add("--contract-out")
    args.add(contract_out)
    args.add("--compatibility-out")
    args.add(compatibility_out)

    postgres_files = ctx.files.postgres
    initdb = _find_postgres_tool(postgres_files, "initdb")
    postgres = _find_postgres_tool(postgres_files, "postgres")
    pg_isready = _find_postgres_tool(postgres_files, "pg_isready")
    pg_ctl = _find_postgres_tool(postgres_files, "pg_ctl")
    socat_files = ctx.files._socat
    socat = _find_distribution_tool(socat_files, "socat", "socat")
    coreutils_files = ctx.files._coreutils
    mktemp = _find_distribution_tool(coreutils_files, "mktemp", "coreutils")
    mkdir = _find_distribution_tool(coreutils_files, "mkdir", "coreutils")
    rm = _find_distribution_tool(coreutils_files, "rm", "coreutils")
    sleep = _find_distribution_tool(coreutils_files, "sleep", "coreutils")

    ctx.actions.run_shell(
        command = _SERVER_LIFECYCLE,
        arguments = [
            initdb.path,
            postgres.path,
            pg_isready.path,
            pg_ctl.path,
            socat.path,
            mktemp.path,
            mkdir.path,
            rm.path,
            sleep.path,
            ctx.executable._generator.path,
            args,
        ],
        inputs = depset(
            direct = database.migrations + database.query_srcs + [database.manifest],
        ),
        outputs = [ir_out, contract_out, compatibility_out],
        tools = depset(
            direct = postgres_files + socat_files + coreutils_files + [ctx.executable._generator],
        ),
        use_default_shell_env = False,
        execution_requirements = {
            "block-network": "1",
        },
        mnemonic = "LeanPgCompatProbe",
        progress_message = "Probing %s with PostgreSQL %s" % (ctx.attr.database.label, ctx.attr.major),
    )
    return [
        DefaultInfo(files = depset([ir_out, contract_out, compatibility_out])),
        _PgCompatSnapshotInfo(schema_ir = ir_out, major = ctx.attr.major),
    ]

_pg_compat_snapshot = rule(
    implementation = _pg_compat_snapshot_impl,
    attrs = {
        "database": attr.label(
            mandatory = True,
            providers = [LeanPgGenInfo],
        ),
        "postgres": attr.label(
            mandatory = True,
            allow_files = True,
            cfg = "exec",
        ),
        "major": attr.int(mandatory = True),
        "_generator": attr.label(
            default = "@lean-pgx//lean/Pgx/Codegen:pgx_codegen",
            executable = True,
            cfg = "exec",
        ),
        "_socat": attr.label(
            default = "@socat//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
        "_coreutils": attr.label(
            default = "@coreutils//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
    },
)

def _runfile_expr(path):
    if path.startswith("../"):
        return '"$RUNFILES_DIR/%s"' % path[3:]
    return '"$RUNFILES_DIR/$TEST_WORKSPACE/%s"' % path

def _pg_compat_compare_test_impl(ctx):
    snapshots = [target[_PgCompatSnapshotInfo].schema_ir for target in ctx.attr.snapshots]
    if len(snapshots) < 2:
        fail("pg_compat_test needs at least two PostgreSQL snapshots")
    script = ctx.actions.declare_file(ctx.label.name + ".sh")
    compare = ctx.executable._compare
    lines = [
        "#!/usr/bin/env bash",
        "set -euo pipefail",
        "COMPARE=%s" % _runfile_expr(compare.short_path),
        "BASE=%s" % _runfile_expr(snapshots[0].short_path),
    ]
    for snapshot in snapshots[1:]:
        lines.append('"$COMPARE" "$BASE" %s' % _runfile_expr(snapshot.short_path))
    ctx.actions.write(script, "\n".join(lines) + "\n", is_executable = True)
    runfiles = ctx.runfiles(files = snapshots + [compare])
    runfiles = runfiles.merge(ctx.attr._compare[DefaultInfo].default_runfiles)
    return [DefaultInfo(executable = script, runfiles = runfiles)]

_pg_compat_compare_test = rule(
    implementation = _pg_compat_compare_test_impl,
    test = True,
    attrs = {
        "snapshots": attr.label_list(
            mandatory = True,
            providers = [_PgCompatSnapshotInfo],
        ),
        "_compare": attr.label(
            default = "@lean-pgx//lean/Pgx/Codegen:pgx_compare",
            executable = True,
            cfg = "target",
        ),
    },
)

def _pg_live_test_impl(ctx):
    database = ctx.attr.database[LeanPgGenInfo]
    stamp = ctx.actions.declare_file(ctx.label.name + ".live-ok")
    script = ctx.actions.declare_file(ctx.label.name + ".sh")
    args = ctx.actions.args()
    for migration in database.migrations:
        args.add("--migration")
        args.add(migration)
    args.add_all(ctx.attr.runner_args)

    postgres_files = ctx.files.postgres
    initdb = _find_postgres_tool(postgres_files, "initdb")
    postgres = _find_postgres_tool(postgres_files, "postgres")
    pg_isready = _find_postgres_tool(postgres_files, "pg_isready")
    pg_ctl = _find_postgres_tool(postgres_files, "pg_ctl")
    socat_files = ctx.files._socat
    socat = _find_distribution_tool(socat_files, "socat", "socat")
    coreutils_files = ctx.files._coreutils
    mktemp = _find_distribution_tool(coreutils_files, "mktemp", "coreutils")
    mkdir = _find_distribution_tool(coreutils_files, "mkdir", "coreutils")
    rm = _find_distribution_tool(coreutils_files, "rm", "coreutils")
    sleep = _find_distribution_tool(coreutils_files, "sleep", "coreutils")
    command = _SERVER_LIFECYCLE + '\nprintf "ok\\n" > "$PGX_STAMP"\n'
    ctx.actions.run_shell(
        command = command,
        arguments = [
            initdb.path,
            postgres.path,
            pg_isready.path,
            pg_ctl.path,
            socat.path,
            mktemp.path,
            mkdir.path,
            rm.path,
            sleep.path,
            ctx.executable.runner.path,
            args,
        ],
        env = {"PGX_STAMP": stamp.path},
        inputs = depset(
            direct = database.migrations + ctx.files.data,
        ),
        outputs = [stamp],
        tools = depset(
            direct = postgres_files + socat_files + coreutils_files + [ctx.executable.runner],
        ),
        use_default_shell_env = False,
        execution_requirements = {
            "block-network": "1",
        },
        mnemonic = "LeanPgLiveTest",
        progress_message = "Running checked PostgreSQL acceptance test %s" % ctx.label,
    )
    ctx.actions.write(
        script,
        "#!/usr/bin/env bash\nset -euo pipefail\nexit 0\n",
        is_executable = True,
    )
    return [DefaultInfo(
        executable = script,
        runfiles = ctx.runfiles(files = [stamp]),
    )]

_pg_live_test = rule(
    implementation = _pg_live_test_impl,
    test = True,
    attrs = {
        "database": attr.label(
            mandatory = True,
            providers = [LeanPgGenInfo],
        ),
        "runner": attr.label(
            mandatory = True,
            executable = True,
            cfg = "exec",
        ),
        "postgres": attr.label(
            default = "@postgresql_18//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
        "runner_args": attr.string_list(),
        "data": attr.label_list(allow_files = True),
        "_socat": attr.label(
            default = "@socat//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
        "_coreutils": attr.label(
            default = "@coreutils//:toolchain",
            allow_files = True,
            cfg = "exec",
        ),
    },
)

def _generation_label(database):
    value = str(database)
    if value.startswith(":"):
        return value + "_gen"
    if ":" in value:
        return value + "_gen"
    if value.startswith("//"):
        target = value.rsplit("/", 1)[-1]
        return value + ":" + target + "_gen"
    return value + "_gen"

def lean_pg_library(
        name,
        module_prefix,
        migrations,
        queries,
        schemas,
        postgres = "@postgresql_18//:toolchain",
        server_majors = None,
        deps = None,
        visibility = None,
        **kwargs):
    """Replays DDL, emits checked Lean modules, then compiles a lean_library."""
    gen_name = name + "_gen"
    _lean_pg_generate(
        name = gen_name,
        module_prefix = module_prefix,
        output_basename = name,
        migrations = migrations,
        queries = queries,
        schemas = schemas,
        postgres = postgres,
        server_majors = server_majors or [17, 18],
        visibility = visibility,
    )
    srcs_name = name + "_srcs"
    native.filegroup(
        name = srcs_name,
        srcs = [":" + gen_name],
        output_group = "lean_srcs",
        visibility = ["//visibility:private"],
    )
    lean_library(
        name = name,
        srcs = [":" + srcs_name],
        strip_module_prefix = native.package_name(),
        deps = ["@lean-pgx//lean:pg_typed"] + (deps or []),
        visibility = visibility,
        **kwargs
    )

def pg_compat_test(
        name,
        database,
        postgres,
        majors = None,
        visibility = None,
        **kwargs):
    """Replays one generated contract on multiple PostgreSQL major versions.

    Compatibility ignores the server-major field itself and compares every
    other Lean-level schema/query semantic in the canonical IR.
    """
    if len(postgres) < 2:
        fail("pg_compat_test requires at least two PostgreSQL distributions")
    selected_majors = majors or [17, 18]
    if len(selected_majors) != len(postgres):
        fail("pg_compat_test majors and postgres lists must have equal length")
    snapshots = []
    for i in range(len(postgres)):
        snapshot_name = name + "_pg" + str(selected_majors[i]) + "_" + str(i + 1)
        _pg_compat_snapshot(
            name = snapshot_name,
            database = _generation_label(database),
            postgres = postgres[i],
            major = selected_majors[i],
            visibility = ["//visibility:private"],
        )
        snapshots.append(":" + snapshot_name)
    _pg_compat_compare_test(
        name = name,
        snapshots = snapshots,
        visibility = visibility,
        **kwargs
    )

def pg_live_test(
        name,
        database,
        runner,
        postgres = "@postgresql_18//:toolchain",
        args = None,
        data = None,
        visibility = None,
        **kwargs):
    """Runs a Lean acceptance executable against a fresh migrated cluster."""
    _pg_live_test(
        name = name,
        database = _generation_label(database),
        runner = runner,
        postgres = postgres,
        runner_args = args or [],
        data = data or [],
        visibility = visibility,
        **kwargs
    )
