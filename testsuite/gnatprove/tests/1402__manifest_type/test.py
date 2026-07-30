import os

from test_support import run_command

# A proof manifest may name a type. A type is its own proof unit, so the
# resolver must match a type path and pass the entry's options to the
# gnatwhy3 process that proves the type's checks. Using a private type also
# guards against its partial and full views, which share a source path, being
# resolved as two anchors and rejected as a spurious ambiguity.

manifest_dir = "manifest"
os.makedirs(manifest_dir, exist_ok=True)

with open(os.path.join(manifest_dir, "pkg.toml"), "w") as f:
    f.write(
        """\
version = 1

[[rule]]
path = "Pkg"
provers = ["cvc5"]
steps = 100

[[rule]]
path = "Pkg.T"
provers = ["cvc5"]
steps = 4242
"""
    )

process = run_command(
    [
        "gnatprove",
        "-k",
        "-P",
        "test.gpr",
        "--debug",
        f"--proof-manifest-dir={manifest_dir}",
        "-u",
        "pkg.adb",
        "--output=brief",
    ]
)

# The type-specific step budget must reach exactly one gnatwhy3 invocation:
# the one proving the type's own checks.
gnatwhy3_lines = [
    line for line in process.out.splitlines() if line.startswith("gnatwhy3 ")
]
matching_lines = [line for line in gnatwhy3_lines if " --steps 4242 " in f" {line} "]

if len(matching_lines) != 1:
    raise AssertionError(process.out)

# The entry must be accepted, not reported stale, unmatched, or ambiguous.
if "invalid proof manifest entry" in process.out:
    raise AssertionError(process.out)
