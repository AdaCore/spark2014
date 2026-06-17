import os

from test_support import gnatprove, run_command

# Each case carries its manifest inline so that the manifest being tested sits
# right next to what is checked about it. Two kinds of cases exist:
#
#  * Diagnostic cases use check_manifest: the manifest is echoed and gnatprove's
#    output is shown, so the whole case can be reviewed from test.out alone.
#
#  * Dispatch-inspection cases use inspect: they run gnatprove with --debug and
#    assert on the proof options that reach the per-subprogram gnatwhy3 calls.
#    Their expectations live in the assertions below, beside the manifest.


def write_manifest(name, manifest):
    folder = name.replace(" ", "_")
    os.makedirs(folder, exist_ok=True)
    with open(os.path.join(folder, "pkg.toml"), "w") as f:
        f.write(manifest)
    return folder


def check_manifest(name, manifest, opt=None, no_output=False):
    folder = write_manifest(name, manifest)
    print(f"===== {name} =====")
    print("--- manifest pkg.toml ---")
    print(manifest if manifest.endswith("\n") else manifest + "\n", end="")
    print("--- output ---")
    gnatprove(
        opt=[
            "-P",
            "test.gpr",
            f"--proof-manifest-dir={folder}",
            *(opt or []),
            "-u",
            "pkg.adb",
        ],
        no_output=no_output,
    )


def inspect(name, manifest):
    """Run gnatprove with --debug and return the per-subprogram gnatwhy3 lines."""
    folder = write_manifest(name, manifest)
    print(f"===== {name} =====")
    process = run_command(
        [
            "gnatprove",
            "-k",
            "-P",
            "test.gpr",
            "--debug",
            f"--proof-manifest-dir={folder}",
            "-u",
            "pkg.adb",
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


def assert_lacks_options(line, *options):
    for option in options:
        if f" {option} " in line:
            raise AssertionError(line)


# A fully resolved entry (path + kind + profile) is accepted silently.
check_manifest(
    "resolved manifest entry",
    """\
version = 1

[[subprogram]]
path = "Pkg.P"
kind = "procedure"
profile = "(_ : Integer)"
timeout = 1
""",
    no_output=True,
)

# A unit-level default and a package-level entry both match; the package entry
# must not override the unit default for the contained subprograms.
lines = inspect(
    "unit default and package entity",
    """\
version = 1

[[subprogram]]
path = "Pkg"
steps = 100

[[subprogram]]
path = "Pkg"
kind = "package"
hierarchical = false
steps = 200
""",
)
assert_has_options(gnatwhy3_line_for(lines, "pkg__r"), "--steps 100")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__r"), "--steps 200")
assert_has_options(gnatwhy3_line_for(lines, "pkg__inner__s"), "--steps 100")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__inner__s"), "--steps 200")

# Same as above but the package entry names the nested package Pkg.Inner.
lines = inspect(
    "unit default and nested package entity",
    """\
version = 1

[[subprogram]]
path = "Pkg"
steps = 100

[[subprogram]]
path = "Pkg.Inner"
kind = "package"
hierarchical = false
steps = 200
""",
)
assert_has_options(gnatwhy3_line_for(lines, "pkg__r"), "--steps 100")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__r"), "--steps 200")
assert_has_options(gnatwhy3_line_for(lines, "pkg__inner__s"), "--steps 100")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__inner__s"), "--steps 200")

# "Pkg.P" without a profile matches both overloads of P and is ambiguous.
check_manifest(
    "ambiguous manifest entry",
    """\
version = 1

[[subprogram]]
path = "Pkg.P"
kind = "procedure"
timeout = 1
""",
)

# An entry naming an entity that does not exist in the unit is reported.
check_manifest(
    "missing manifest entity",
    """\
version = 1

[[subprogram]]
path = "Pkg.Missing"
kind = "procedure"
timeout = 1
""",
)

# An entry matching an entity excluded by --limit-name is reported.
check_manifest(
    "manifest entity not selected",
    """\
version = 1

[[subprogram]]
path = "Pkg.Q"
kind = "procedure"
timeout = 1
""",
    opt=["--limit-name=P"],
)

# A matching entry applies its proof options to the selected subprogram.
check_manifest(
    "manifest applies steps override",
    """\
version = 1

[[subprogram]]
path = "Pkg.R"
timeout = 5
steps = 100
provers = ["cvc5"]
""",
    opt=["--report=all", "--limit-name=R"],
)

# A package-level prefix entry covers every subprogram it contains.
lines = inspect(
    "package prefix covers multiple subprograms",
    """\
version = 1

[[subprogram]]
path = "Pkg"
timeout = 5
steps = 100
provers = ["cvc5"]
""",
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__r"), "--timeout 5", "--steps 100", "--prover cvc5"
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--timeout 5",
    "--steps 100",
    "--prover cvc5",
)

# A nested-package prefix covers only the subprograms below it.
lines = inspect(
    "nested prefix covers single subprogram",
    """\
version = 1

[[subprogram]]
path = "Pkg.Inner"
timeout = 5
steps = 100
provers = ["cvc5"]
""",
)
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__r"), "--timeout 5")
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--timeout 5",
    "--steps 100",
    "--prover cvc5",
)

# A prefix entry with a kind applies to its anchor only, not to the entities it
# covers: here the function kind must not push options onto Pkg.Inner.F.
lines = inspect(
    "prefix kind applies to anchor only",
    """\
version = 1

[[subprogram]]
path = "Pkg.Inner"
kind = "function"
timeout = 9
steps = 321
provers = ["cvc5"]
""",
)
assert_lacks_options(
    gnatwhy3_line_for(lines, "pkg__inner__f"), "--timeout 9", "--steps 321"
)

# A more specific entry wins over a broader one for the subprogram it names.
lines = inspect(
    "specific entry overrides broader entry",
    """\
version = 1

[[subprogram]]
path = "Pkg"
timeout = 5
steps = 100
provers = ["cvc5"]

[[subprogram]]
path = "Pkg.R"
timeout = 5
steps = 200
provers = ["cvc5"]
""",
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__r"), "--timeout 5", "--steps 200", "--prover cvc5"
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--timeout 5",
    "--steps 100",
    "--prover cvc5",
)

# Two entries of equal specificity matching the same subprogram are ambiguous.
check_manifest(
    "two same-specificity entries are ambiguous",
    """\
version = 1

[[subprogram]]
path = "Pkg.R"
timeout = 5

[[subprogram]]
path = "Pkg.R"
kind = "procedure"
timeout = 10
""",
)
