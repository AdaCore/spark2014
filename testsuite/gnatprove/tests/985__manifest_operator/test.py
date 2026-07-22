import os

from test_support import gnatprove, run_command

# This test checks that proof-manifest entries can target user-defined operator
# subprograms ("&", "-", ...). An operator has no plain identifier name, so its
# manifest path carries the operator spelled with its quotes as the final
# segment, e.g. Pkg."&". The reader must accept such a path, the resolver must
# match it to the operator entity, and overloaded operators must still be told
# apart by their profile.

# A single entry for a non-overloaded operator, targeted by its quoted path.
SINGLE = """\
version = 1

[[rule]]
path = "Pkg.\\"&\\""
kind = "function"
steps = 333
provers = ["cvc5"]
"""

# One entry per overload of "-", disambiguated by profile: the binary overload
# and the unary overload share the path Pkg."-".
PER_OVERLOAD = """\
version = 1

[[rule]]
path = "Pkg.\\"-\\""
kind = "function"
profile = "(_ : Pkg.T; _ : Pkg.T) return Pkg.T"
steps = 111
provers = ["cvc5"]

[[rule]]
path = "Pkg.\\"-\\""
kind = "function"
profile = "(_ : Pkg.T) return Pkg.T"
steps = 222
provers = ["cvc5"]
"""

# A malformed operator path: "%" is not an Ada operator symbol. The reader must
# still reject such a path.
MALFORMED = """\
version = 1

[[rule]]
path = "Pkg.\\"%\\""
kind = "function"
steps = 1
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


# The manifest reader accepts an operator path and gnatprove proves the unit.
check_manifest("operator entry resolves cleanly", SINGLE)

# The entry for the non-overloaded operator "&" is applied to that operator.
# Pkg."&" is translated to pkg__Oconcat.
lines = inspect("operator entry targets its operator", SINGLE)
assert_has_options(gnatwhy3_line_for(lines, "pkg__Oconcat"), "--steps 333")

# Each per-overload entry applies its own options to its own overload only.
# The binary "-" is translated to pkg__Osubtract, the unary "-" to
# pkg__Osubtract__2.
lines = inspect("operator overloads target their own overload", PER_OVERLOAD)
assert_has_options(gnatwhy3_line_for(lines, "pkg__Osubtract"), "--steps 111")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__Osubtract"), "--steps 222")
assert_has_options(gnatwhy3_line_for(lines, "pkg__Osubtract__2"), "--steps 222")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__Osubtract__2"), "--steps 111")

# A malformed operator path is still rejected by the reader.
folder = write_manifest("malformed operator path is rejected", MALFORMED)
process = run_command(
    [
        "gnatprove",
        "-P",
        "test.gpr",
        f"--proof-manifest-dir={folder}",
        "-u",
        "pkg.adb",
    ],
)
assert 'field "path" must be a dot-separated Ada name' in process.out, process.out
print("===== malformed operator path is rejected =====")
print("OK")
