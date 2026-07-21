import os
import re
from pathlib import Path

from test_support import gnatprove, run_command

# A proof manifest file is named after the Ada unit it configures. This test
# checks that the feature works for an actual *child* unit (Pkg.Child): the
# dash in the manifest file name (pkg-child.toml) stands for the dot in the
# unit name, and the name is derived from the unit rather than from the source
# file. To make the unit name and the source file name diverge, the project
# uses a non-default naming scheme, so Pkg.Child lives in child_spec.ada /
# child_impl.ada.
#
# It covers:
#   1. a hand-written manifest (pkg-child.toml) is applied to Pkg.Child's
#      subprograms, i.e. the manifest key derived from the file name matches
#      the one derived from the dotted unit name;
#   2. --generate-manifest-dir names the generated manifest after the unit in
#      lower case (pkg-child.toml), not after the source file (child_impl.toml);
#   3. the generated manifest reads back and is applied (round-trip).

BODY = "child_impl.ada"

# The child subprogram's per-check file stem. Any prefix (e.g. a scope prefix)
# is tolerated by matching on the trailing part only.
STEM = "pkg__child__r"


def inspect(manifest_dir):
    """Return the per-subprogram gnatwhy3 lines for a --debug run."""
    process = run_command(
        [
            "gnatprove",
            "-f",
            "-k",
            "-P",
            "test.gpr",
            "--debug",
            f"--proof-manifest-dir={manifest_dir}",
            "-u",
            BODY,
            "--output=brief",
        ]
    )
    return [line for line in process.out.splitlines() if line.startswith("gnatwhy3 ")]


def gnatwhy3_line_for(lines, file_stem):
    matches = [line for line in lines if f"{file_stem}.gnat-json " in line]
    if len(matches) != 1:
        raise AssertionError("\n".join(lines))
    return f" {matches[0]} "


def assert_has_options(line, *options):
    for option in options:
        if f" {option} " not in line:
            raise AssertionError(line)


def manifest_block(line):
    """Return the proof options a manifest contributes, appended after --entity."""
    tail = re.split(r"--entity \d+ ?", line, maxsplit=1)[1]
    return [tok for tok in tail.split() if not tok.endswith(".gnat-json")]


# 1. A hand-written manifest named after the child unit is applied to it.
print("===== manifest applies to child unit =====")
os.makedirs("manifest", exist_ok=True)
with open(os.path.join("manifest", "pkg-child.toml"), "w") as f:
    f.write(
        """\
version = 1

[[rule]]
path = "Pkg.Child"
timeout = 7
steps = 777
provers = ["z3"]
"""
    )
lines = inspect("manifest")
assert_has_options(
    gnatwhy3_line_for(lines, STEM), "--timeout 7", "--steps 777", "--prover z3"
)

# 2. Generation names the manifest after the unit in lower case
#    (pkg-child.toml), not after the source file (child_impl.toml), and
#    attributes entities to the unit so that a rule is produced.
print("===== generate manifest for child unit =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--mode=prove",
        "--level=0",
        "--generate-manifest-dir=generated",
        "-u",
        BODY,
    ],
    no_output=True,
)
generated = Path("generated/pkg-child.toml")
assert generated.is_file(), sorted(p.name for p in Path("generated").iterdir())
assert 'path = "Pkg.Child"' in generated.read_text(), generated.read_text()

# 3. The generated manifest reads back cleanly and is applied to the unit.
print("===== generated manifest round-trips =====")
lines = inspect("generated")
assert manifest_block(gnatwhy3_line_for(lines, STEM)), lines
