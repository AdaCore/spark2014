from test_support import gnatprove, run_command


def gnatwhy3_lines(manifest):
    process = run_command(
        [
            "gnatprove",
            "-k",
            "-P",
            "test.gpr",
            "--debug",
            f"--proof-manifest-dir={manifest}",
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


print("===== resolved manifest entry =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=resolved",
        "-u",
        "pkg.adb",
    ],
    no_output=True,
)

print("===== unit default and package entity =====")
lines = gnatwhy3_lines("unit_and_package_match")
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__r"),
    "--steps 100",
)
assert_lacks_options(
    gnatwhy3_line_for(lines, "pkg__r"),
    "--steps 200",
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--steps 100",
)
assert_lacks_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--steps 200",
)

print("===== unit default and nested package entity =====")
lines = gnatwhy3_lines("unit_and_nested_package_match")
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__r"),
    "--steps 100",
)
assert_lacks_options(
    gnatwhy3_line_for(lines, "pkg__r"),
    "--steps 200",
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--steps 100",
)
assert_lacks_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--steps 200",
)

print("===== ambiguous manifest entry =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=ambiguous",
        "-u",
        "pkg.adb",
    ]
)

print("===== missing manifest entity =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=missing_entity",
        "-u",
        "pkg.adb",
    ]
)

print("===== manifest entity not selected =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=not_selected",
        "--limit-name=P",
        "-u",
        "pkg.adb",
    ]
)

print("===== manifest applies steps override =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=apply_steps",
        "--report=all",
        "--limit-name=R",
        "-u",
        "pkg.adb",
    ]
)

print("===== package prefix covers multiple subprograms =====")
lines = gnatwhy3_lines("pkg_prefix")
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__r"),
    "--timeout 5",
    "--steps 100",
    "--prover cvc5",
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--timeout 5",
    "--steps 100",
    "--prover cvc5",
)

print("===== nested prefix covers single subprogram =====")
lines = gnatwhy3_lines("inner_prefix")
assert_lacks_options(gnatwhy3_line_for(lines, "pkg__r"), "--timeout 5")
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--timeout 5",
    "--steps 100",
    "--prover cvc5",
)

print("===== prefix kind applies to anchor only =====")
lines = gnatwhy3_lines("wrong_anchor_kind")
assert_lacks_options(
    gnatwhy3_line_for(lines, "pkg__inner__f"),
    "--timeout 9",
    "--steps 321",
)

print("===== specific entry overrides broader entry =====")
lines = gnatwhy3_lines("override")
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__r"),
    "--timeout 5",
    "--steps 200",
    "--prover cvc5",
)
assert_has_options(
    gnatwhy3_line_for(lines, "pkg__inner__s"),
    "--timeout 5",
    "--steps 100",
    "--prover cvc5",
)

print("===== two same-specificity entries are ambiguous =====")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--proof-manifest-dir=tie_ambiguity",
        "-u",
        "pkg.adb",
    ]
)
