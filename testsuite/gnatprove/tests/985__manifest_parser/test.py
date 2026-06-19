import os

from test_support import gnatprove

# Each manifest case is fully described here: a name, the manifest file name,
# and its inline TOML content. The manifest is written to a per-case folder and
# echoed into the output, so that test.out shows, for every case, the manifest
# that was fed to gnatprove right next to the resulting diagnostic. Reviewing a
# case therefore only requires reading a single contiguous section of test.out.


def run(name, opt):
    print(f"===== {name} =====")
    gnatprove(
        opt=["-P", "test.gpr", *opt, "--mode=check", "-u", "main.adb"],
        no_output=False,
    )


def check_manifest(name, manifest, manifest_file="main.toml", valid=False):
    """Write MANIFEST to a folder named after NAME, echo it, and run gnatprove.

    When VALID is set, the manifest is expected to be accepted and gnatprove's
    output is suppressed, so an empty output section signals success.
    """
    folder = name.replace(" ", "_")
    os.makedirs(folder, exist_ok=True)
    with open(os.path.join(folder, manifest_file), "w") as f:
        f.write(manifest)

    print(f"===== {name} =====")
    print(f"--- manifest {manifest_file} ---")
    print(manifest if manifest.endswith("\n") else manifest + "\n", end="")
    print("--- output ---")
    gnatprove(
        opt=[
            "-P",
            "test.gpr",
            f"--proof-manifest-dir={folder}",
            "--mode=check",
            "-u",
            "main.adb",
        ],
        no_output=valid,
    )


# Valid manifest exercising every supported field. It is accepted, so no output
# is expected.

check_manifest(
    "valid manifest",
    """\
version = 1

[[rule]]
path = "Main"
kind = "procedure"
profile = "()"
timeout = 1
steps = 100
memlimit = 1000
level = 2
provers = ["cvc5", "z3"]

[[rule]]
path = "Main.Inner"
kind = "procedure"
profile = "(_ : Integer)"
steps = 200
""",
    valid=True,
)

# Note: manifests combining a unit default with a package entry (with the
# "hierarchical" field) are exercised, including their dispatch behavior, by
# 985__manifest_dispatch, so they are not repeated here.

# Invalid manifests: each triggers a specific parser diagnostic.

check_manifest(
    "unknown field",
    """\
version = 1

[[rule]]
path = "Main"
unknown = 1
""",
)

check_manifest(
    "bad provers syntax",
    """\
version = 1

[[rule]]
path = "Main"
provers = "cvc5"
""",
)

check_manifest(
    "missing path",
    """\
version = 1

[[rule]]
timeout = 1
""",
)

check_manifest(
    "missing version",
    """\
[[rule]]
path = "Main"
""",
)

check_manifest(
    "unsupported version",
    """\
version = 2

[[rule]]
path = "Main"
""",
)

# Folder-level problems that do not involve manifest content.

run("missing folder", ["--proof-manifest-dir=missing_manifest"])
run("file instead of folder", ["--proof-manifest-dir=main.adb"])

check_manifest(
    "wrong unit",
    """\
version = 1

[[rule]]
path = "Main"
steps = 1
""",
    manifest_file="other.toml",
)

check_manifest(
    "bad kind",
    """\
version = 1

[[rule]]
path = "Main"
kind = "task"
steps = 1
""",
)

check_manifest(
    "profile without kind",
    """\
version = 1

[[rule]]
path = "Main"
profile = "()"
steps = 1
""",
)

check_manifest(
    "bad hierarchical",
    """\
version = 1

[[rule]]
path = "Main"
hierarchical = "false"
steps = 1
""",
)

check_manifest(
    "package profile",
    """\
version = 1

[[rule]]
path = "Main"
kind = "package"
profile = "()"
steps = 1
""",
)

check_manifest(
    "no options",
    """\
version = 1

[[rule]]
path = "Main"
""",
)

check_manifest(
    "bad level",
    """\
version = 1

[[rule]]
path = "Main"
level = 5
""",
)

check_manifest(
    "duplicate entry",
    """\
version = 1

[[rule]]
path = "Main"
steps = 1

[[rule]]
path = "Main"
timeout = 1
""",
)

check_manifest(
    "duplicate prover",
    """\
version = 1

[[rule]]
path = "Main"
provers = ["cvc5", "cvc5"]
""",
)

check_manifest(
    "bad path",
    """\
version = 1

[[rule]]
path = "Main..Inner"
steps = 1
""",
)

# The manifest folder may not be set through the project file.

print("===== project switch rejected =====")
gnatprove(opt=["-P", "manifest_in_project.gpr", "--mode=check", "-u", "main.adb"])
