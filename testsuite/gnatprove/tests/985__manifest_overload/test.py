import os

from test_support import gnatprove, run_command

# This test checks that proof-manifest entries targeting individual overloads
# of a subprogram are resolved and applied correctly. Overloads share a dotted
# path (here "Pkg.Set") and are told apart only by their profile. Each
# per-overload entry must apply its options to its own overload and must not
# collide with the sibling overload's entry. The bodies nest further overloads
# ("Pkg.Set.Helper"), so the same disambiguation must also work for a
# subprogram nested in an overload and for overloads nested in an overload.

# One entry per overload, disambiguated by profile, at both nesting levels.
PER_OVERLOAD = """\
version = 1

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Integer)"
steps = 111
provers = ["cvc5"]

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Boolean)"
steps = 222
provers = ["cvc5"]

[[rule]]
path = "Pkg.Set.Helper"
kind = "procedure"
profile = "(_ : Integer)"
steps = 333
provers = ["cvc5"]

[[rule]]
path = "Pkg.Set.Helper"
kind = "procedure"
profile = "(_ : Boolean)"
steps = 444
provers = ["cvc5"]
"""


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
    # The file argument is a native path, so match on a copy of the line with
    # the directory separators normalized.
    needle = f"/{file_stem}.gnat-json "
    matches = [line for line in lines if needle in line.replace("\\", "/")]
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


# Four per-overload entries -- two outer, two nested -- are each fully resolved
# by their profile and must be accepted without any ambiguity diagnostic.
check_manifest("per-overload entries resolve cleanly", PER_OVERLOAD)

# Each per-overload entry applies its own options to its own overload only,
# at both nesting levels. The four overloads translate to distinct units:
#   Pkg.Set(Integer)               -> pkg__set
#   Pkg.Set(Boolean)               -> pkg__set__2
#   Pkg.Set.Helper(Integer)        -> pkg__set__helper
#   Pkg.Set.Helper(Boolean)        -> pkg__set__helper__2
# The nested Helper entries are more specific than the outer Set entries, so a
# Set entry never leaks its options onto a nested Helper overload.
lines = inspect("per-overload entries target their own overload", PER_OVERLOAD)

set_int = gnatwhy3_line_for(lines, "pkg__set")
assert_has_options(set_int, "--steps 111")
assert_lacks_options(set_int, "--steps 222", "--steps 333", "--steps 444")

set_bool = gnatwhy3_line_for(lines, "pkg__set__2")
assert_has_options(set_bool, "--steps 222")
assert_lacks_options(set_bool, "--steps 111", "--steps 333", "--steps 444")

helper_int = gnatwhy3_line_for(lines, "pkg__set__helper")
assert_has_options(helper_int, "--steps 333")
assert_lacks_options(helper_int, "--steps 111", "--steps 222", "--steps 444")

helper_bool = gnatwhy3_line_for(lines, "pkg__set__helper__2")
assert_has_options(helper_bool, "--steps 444")
assert_lacks_options(helper_bool, "--steps 111", "--steps 222", "--steps 333")
