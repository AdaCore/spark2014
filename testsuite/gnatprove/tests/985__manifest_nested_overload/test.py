import os

from test_support import gnatprove, run_command

# This test checks that a proof manifest can target a subprogram nested inside
# an overloaded parent by *nesting* its rule inside the parent's rule. Both
# overloads of Pkg.Set nest a Helper with the same profile, so the dotted path
# "Pkg.Set.Helper" is inherently ambiguous: only the enclosing Set overload
# distinguishes the two Helpers. A flat entry cannot pick one; a nested entry
# resolves to the Helper enclosed by the Set overload its rule sits under.

# Nested manifest: each Helper rule sits inside its own Set rule, so each Helper
# is resolved as the entity enclosed by that Set overload.
NESTED = """\
version = 1

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Integer)"
steps = 111
provers = ["cvc5"]

  [[rule.rule]]
  path = "Pkg.Set.Helper"
  kind = "procedure"
  profile = "(_ : Integer)"
  steps = 333
  provers = ["cvc5"]

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Boolean)"
steps = 222
provers = ["cvc5"]

  [[rule.rule]]
  path = "Pkg.Set.Helper"
  kind = "procedure"
  profile = "(_ : Integer)"
  steps = 444
  provers = ["cvc5"]
"""

# The same Helper path spelled as a single flat entry: it matches the Helper in
# both Set overloads and is therefore ambiguous.
FLAT = """\
version = 1

[[rule]]
path = "Pkg.Set.Helper"
kind = "procedure"
profile = "(_ : Integer)"
steps = 333
provers = ["cvc5"]
"""

# A parent rule that carries no proof option of its own, only nesting a Helper
# rule. The parent exists solely to anchor the Helper within the Boolean
# overload of Set.
ANCHOR_ONLY = """\
version = 1

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Boolean)"

  [[rule.rule]]
  path = "Pkg.Set.Helper"
  kind = "procedure"
  profile = "(_ : Integer)"
  steps = 444
  provers = ["cvc5"]
"""

# A parent rule that applies to itself only, yet still anchors a nested rule.
# The nested rule is resolved within that overload of Set, while the options of
# the parent stay on Set itself and do not reach the enclosed Helper. The nested
# rule deliberately leaves the memory limit undefined, so that the absence of
# the parent's memory limit on the Helper can be observed.
NON_HIERARCHICAL = """\
version = 1

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Integer)"
hierarchical = false
steps = 111
memlimit = 1234
provers = ["cvc5"]

  [[rule.rule]]
  path = "Pkg.Set.Helper"
  kind = "procedure"
  profile = "(_ : Integer)"
  steps = 333
  provers = ["cvc5"]
"""

# A nested rule whose path does not extend its parent's path is rejected at
# parse time.
BAD_PREFIX = """\
version = 1

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Integer)"
steps = 111
provers = ["cvc5"]

  [[rule.rule]]
  path = "Pkg.Other.Helper"
  kind = "procedure"
  steps = 333
  provers = ["cvc5"]
"""

# A rule nests nothing, so it does not qualify for the exemption that lets a
# rule with nested rules omit its proof options. An empty nested array is
# rejected rather than silently standing for a rule that applies no option.
EMPTY_NESTED = """\
version = 1

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Boolean)"
rule = []
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


# The nested entries resolve without any ambiguity diagnostic.
check_manifest("nested entries resolve cleanly", NESTED)

# Each Helper is resolved to the overload its rule is nested under, even though
# both Helpers share the path "Pkg.Set.Helper" and the same profile. The four
# overloads translate to distinct units:
#   Pkg.Set(Integer)                  -> pkg__set
#   Pkg.Set(Boolean)                  -> pkg__set__2
#   Pkg.Set(Integer).Helper(Integer)  -> pkg__set__helper
#   Pkg.Set(Boolean).Helper(Integer)  -> pkg__set__2__helper
lines = inspect("nested entries target the right overload", NESTED)

set_int = gnatwhy3_line_for(lines, "pkg__set")
assert_has_options(set_int, "--steps 111")
assert_lacks_options(set_int, "--steps 222", "--steps 333", "--steps 444")

set_bool = gnatwhy3_line_for(lines, "pkg__set__2")
assert_has_options(set_bool, "--steps 222")
assert_lacks_options(set_bool, "--steps 111", "--steps 333", "--steps 444")

helper_in_int = gnatwhy3_line_for(lines, "pkg__set__helper")
assert_has_options(helper_in_int, "--steps 333")
assert_lacks_options(helper_in_int, "--steps 111", "--steps 222", "--steps 444")

helper_in_bool = gnatwhy3_line_for(lines, "pkg__set__2__helper")
assert_has_options(helper_in_bool, "--steps 444")
assert_lacks_options(helper_in_bool, "--steps 111", "--steps 222", "--steps 333")

# A parent rule may carry no option of its own and serve only to anchor a
# nested rule: here only the Helper in the Boolean overload receives options.
lines = inspect("anchor-only parent applies no options of its own", ANCHOR_ONLY)
assert_has_options(gnatwhy3_line_for(lines, "pkg__set__2__helper"), "--steps 444")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__set__2"), "--steps 444")

# A rule that is not hierarchical applies to its own entity only, but it still
# anchors the rule nested inside it: the Helper of the Integer overload gets the
# options of the nested rule, and none of the parent's.
lines = inspect("non-hierarchical parent anchors a nested rule", NON_HIERARCHICAL)
set_int = gnatwhy3_line_for(lines, "pkg__set")
assert_has_options(set_int, "--steps 111", "--memlimit 1234")
helper_in_int = gnatwhy3_line_for(lines, "pkg__set__helper")
assert_has_options(helper_in_int, "--steps 333")
assert_lacks_options(helper_in_int, "--steps 111", "--memlimit 1234")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__set__2__helper"), "--steps 333")

# The same path as a single flat entry matches the Helper in both overloads and
# is reported as ambiguous.
check_manifest("flat entry is ambiguous", FLAT)

# A nested rule whose path does not extend its parent's path is rejected.
check_manifest("nested path must extend parent", BAD_PREFIX, opt=["--mode=check"])

# A rule that nests an empty array of rules is rejected.
check_manifest(
    "nested rule array must not be empty", EMPTY_NESTED, opt=["--mode=check"]
)

# The options file handed to gnat2why is named after a hash of the options, and
# is reused when a file of that name already exists. Nesting has to take part in
# that hash, otherwise editing a manifest to change only the nesting reuses the
# options file of the previous run, and the new nesting is silently ignored. The
# two manifests below are written to the same folder and share their layout, so
# every other hashed field, including the recorded location of each rule, is
# identical: only the header of the second rule differs.
SAME_LAYOUT_NESTED = """\
version = 1

[[rule]]
path = "Pkg.Set"
kind = "procedure"
profile = "(_ : Integer)"
steps = 111
provers = ["cvc5"]

  [[rule.rule]]
  path = "Pkg.Set.Helper"
  kind = "procedure"
  profile = "(_ : Integer)"
  steps = 333
  provers = ["cvc5"]
"""

SAME_LAYOUT_FLAT = SAME_LAYOUT_NESTED.replace("[[rule.rule]]", "[[rule]]")

FOLDER = "nesting takes part in the options file hash"

# Nested, the Helper rule resolves to the Helper of the Integer overload.
lines = inspect(FOLDER, SAME_LAYOUT_NESTED)
assert_has_options(gnatwhy3_line_for(lines, "pkg__set__helper"), "--steps 333")

# Flat, the same rule matches both Helpers, so it is ambiguous and ignored, and
# the Helper falls back to the hierarchical rule on the Integer overload.
lines = inspect(FOLDER, SAME_LAYOUT_FLAT)
assert_has_options(gnatwhy3_line_for(lines, "pkg__set__helper"), "--steps 111")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__set__helper"), "--steps 333")
