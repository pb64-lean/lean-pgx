"""Self-contained Nix tool repositories used by lean-pgx's Bazel rules.

The extension deliberately owns namespaced repositories instead of relying on
the process-wide default repositories exposed by rules_nixpkgs.  Consequently,
lean-pgx has the same repository mapping as a root module and as a dependency;
downstream modules do not need to repeat the PostgreSQL/Nix declarations.
"""

load(
    "@rules_nixpkgs_core//:nixpkgs.bzl",
    "nixpkgs_local_repository",
    "nixpkgs_package",
)

_POSTGRES_BUILD = """\
filegroup(
    name = "toolchain",
    srcs = glob(["bin/**", "lib/**", "share/**"]),
    visibility = ["//visibility:public"],
)
"""

_SOCAT_BUILD = """\
filegroup(
    name = "toolchain",
    srcs = ["bin/socat", "bin/socat1"],
    visibility = ["//visibility:public"],
)
"""

_COREUTILS_BUILD = """\
filegroup(
    name = "toolchain",
    srcs = [
        "bin/coreutils",
        "bin/mkdir",
        "bin/mktemp",
        "bin/rm",
        "bin/sleep",
    ],
    visibility = ["//visibility:public"],
)
"""

_REPOSITORIES = [
    "lean_pgx_postgresql_17",
    "lean_pgx_postgresql_18",
    "lean_pgx_socat",
    "lean_pgx_coreutils",
]

def _package(name, attribute_path, build_file_content):
    nixpkgs_package(
        name = name,
        attribute_path = attribute_path,
        build_file_content = build_file_content,
        repository = "@lean_pgx_postgres_nixpkgs",
    )

def _lean_pgx_tools_impl(module_ctx):
    nixpkgs_local_repository(
        name = "lean_pgx_postgres_nixpkgs",
        nix_file = Label("//:postgres.nix"),
        nix_file_deps = [Label("//:postgres.json")],
    )
    _package("lean_pgx_postgresql_17", "postgresql_17", _POSTGRES_BUILD)
    _package("lean_pgx_postgresql_18", "postgresql_18", _POSTGRES_BUILD)
    _package("lean_pgx_socat", "socat", _SOCAT_BUILD)
    _package("lean_pgx_coreutils", "coreutils", _COREUTILS_BUILD)

    return module_ctx.extension_metadata(
        root_module_direct_deps = _REPOSITORIES,
        root_module_direct_dev_deps = [],
    )

lean_pgx_tools = module_extension(
    doc = "Provides lean-pgx's pinned PostgreSQL and process tools.",
    implementation = _lean_pgx_tools_impl,
)
