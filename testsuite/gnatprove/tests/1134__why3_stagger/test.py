"""Check that the --why3-stagger-* switches reach gnatwhy3.

The staggering behavior itself is not exercised here; this test only checks
that the command-line switches translate into the expected gnatwhy3 arguments,
and that out-of-range values are rejected with a command-line error rather than
crashing gnatprove during configuration.
"""

from test_support import generate_project_file, run_command

generate_project_file()


def stagger_blob(*extra):
    """Run gnatprove with --debug and return the gnatwhy3 command lines.

    The lines are collapsed into a single space-padded string; the staggering
    switches are invocation-wide, so every gnatwhy3 call carries the same value
    and a substring check on the blob is enough.
    """
    process = run_command(
        [
            "gnatprove",
            "-P",
            "test.gpr",
            "-f",
            "--debug",
            "--output=brief",
            *extra,
        ]
    )
    lines = [line for line in process.out.splitlines() if line.startswith("gnatwhy3 ")]
    if not lines:
        raise AssertionError("no gnatwhy3 invocation found:\n" + process.out)
    return " " + " ".join(lines) + " "


def check_forwarding(name, extra, present=(), absent=()):
    print(f"===== {name} =====")
    blob = stagger_blob(*extra)
    for opt in present:
        if f" {opt} " not in blob:
            raise AssertionError(f"missing {opt!r} in:\n{blob}")
    for opt in absent:
        if f" {opt} " in blob:
            raise AssertionError(f"unexpected {opt!r} in:\n{blob}")


def check_error(name, extra):
    print(f"===== {name} =====")
    process = run_command(["gnatprove", "-P", "test.gpr", *extra])
    printed = False
    for line in process.out.splitlines():
        if line.startswith("error:"):
            print(line)
            printed = True
    if not printed:
        # Surface the raw output so a regression (e.g. a range check failure
        # instead of the diagnostic) shows up in the diff.
        print(process.out)


# Omitting --why3-stagger-ms uses the 250ms default; window staggering is off.
check_forwarding(
    "default staggering",
    [],
    present=["--stagger-ms 250"],
    absent=["--stagger-window"],
)

# An explicit zero disables time staggering.
check_forwarding(
    "explicit zero milliseconds",
    ["--why3-stagger-ms=0"],
    absent=["--stagger-ms"],
)

# A positive millisecond value is forwarded as given.
check_forwarding(
    "explicit milliseconds",
    ["--why3-stagger-ms=500"],
    present=["--stagger-ms 500"],
)

# A positive window is forwarded alongside the default milliseconds.
check_forwarding(
    "positive window",
    ["--why3-stagger-window=3"],
    present=["--stagger-ms 250", "--stagger-window 3"],
)

# Out-of-range values are rejected with a command-line error, not a crash.
check_error("negative milliseconds", ["--why3-stagger-ms=-1"])
check_error("negative window", ["--why3-stagger-window=-1"])
check_error("zero window", ["--why3-stagger-window=0"])
