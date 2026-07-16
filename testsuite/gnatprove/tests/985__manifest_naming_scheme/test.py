import os
import re
from pathlib import Path

from test_support import gnatprove, run_command

# A proof manifest file is named after the Ada unit it configures, not after
# the source file that unit lives in. This test checks that the feature keeps
# working when the project uses a non-default naming scheme, i.e. when the
# unit's source files do not follow the default "<unit>.ads/<unit>.adb"
# convention.
#
# The unit Pkg lives in unit_spec.ada / unit_body.ada. The test covers:
#   1. a hand-written manifest (pkg.toml) is applied to Pkg's subprograms,
#      whose gnatwhy3 file stems (pkg__...) derive from the unit name rather
#      than from the source file name;
#   2. --generate-manifest-dir names the generated manifest after the unit
#      (pkg.toml), not after the source file (unit_body.toml);
#   3. the generated manifest reads back and is applied (round-trip).

BODY = "unit_body.ada"


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
    matches = [line for line in lines if f"/{file_stem}.gnat-json " in line]
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


# 1. A hand-written manifest named after the unit is applied to its
#    subprograms.
print("===== manifest applies under naming scheme =====")
os.makedirs("manifest", exist_ok=True)
with open(os.path.join("manifest", "pkg.toml"), "w") as f:
    f.write(
        """\
version = 1

[[rule]]
path = "Pkg"
timeout = 7
steps = 777
provers = ["z3"]
"""
    )
lines = inspect("manifest")
for stem in ("pkg__r", "pkg__inner__s"):
    assert_has_options(
        gnatwhy3_line_for(lines, stem), "--timeout 7", "--steps 777", "--prover z3"
    )

# 2. Generation names the manifest after the unit (pkg.toml), not after the
#    source file (unit_body.toml), and attributes entities to the unit so that
#    a rule is actually produced.
print("===== generate manifest under naming scheme =====")
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
generated = Path("generated/pkg.toml")
assert generated.is_file(), sorted(p.name for p in Path("generated").iterdir())
assert 'path = "Pkg"' in generated.read_text(), generated.read_text()

# 3. The generated manifest reads back cleanly and is applied to the unit.
print("===== generated manifest round-trips =====")
lines = inspect("generated")
assert manifest_block(gnatwhy3_line_for(lines, "pkg__r")), lines
