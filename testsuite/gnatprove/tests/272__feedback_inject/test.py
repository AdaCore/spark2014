import os
import shutil
import sys

from test_support import default_refiners_no_sort, prove_all

# Absolute paths to the fake prover and its driver, which the test harness has
# copied next to this script.
here = os.getcwd()
fake_prover = os.path.join(here, "fake_prover.py")
fake_driver = os.path.join(here, "fake.drv")

# Each fake prover prints a fixed marker that fake.drv maps to a single prover
# answer. compress() in gnatwhy3 then turns that answer into an unproved_status:
#   gaveup       -> Unknown -> Gave_up
#   timeout      -> Timeout -> Limit{time}
#   steplimit    -> StepLimitExceeded -> Limit{step}
#   outofmemory  -> OutOfMemory -> Limit{memory}
# Combining several provers on the same check ORs the limit flags together,
# which exercises the combined-limit branches of To_User_Msg.
FAKE_PROVERS = ["gaveup", "timeout", "steplimit", "outofmemory"]


def quote(value):
    # why3 configuration files only accept double-quoted strings. We cannot use
    # repr() (the !r conversion flag) here, as it emits single quotes that the
    # why3 parser rejects, so build the double-quoted value explicitly.
    return '"' + value + '"'


def prover_section(behavior):
    name = "fake_" + behavior
    command = f"{sys.executable} {fake_prover} {behavior} %f"
    return "\n".join(
        [
            "[prover]",
            f"name = {quote(name)}",
            'version = "1.0"',
            'alternative = ""',
            f"command = {quote(command)}",
            f"command_steps = {quote(command)}",
            f"driver = {quote(fake_driver)}",
            f"shortcut = {quote(name)}",
            "interactive = false",
            "in_place = false",
            'editor = ""',
            "",
        ]
    )


why3_conf = os.path.join(here, "fake.why3.conf")
with open(why3_conf, "w") as f:
    for behavior in FAKE_PROVERS:
        f.write(prover_section(behavior))

# Each scenario selects one or more fake provers; multiple provers exercise the
# merging of limit flags for a single check.
SCENARIOS = [
    (["fake_gaveup"], "gave up"),
    (["fake_steplimit"], "step limit"),
    (["fake_timeout"], "time limit"),
    (["fake_outofmemory"], "memory limit"),
    (["fake_timeout", "fake_steplimit"], "time and step limit"),
    (["fake_timeout", "fake_outofmemory"], "time and memory limit"),
    (["fake_steplimit", "fake_outofmemory"], "step and memory limit"),
    (
        ["fake_timeout", "fake_steplimit", "fake_outofmemory"],
        "time, step and memory limit",
    ),
]

for provers, label in SCENARIOS:
    # Start from a clean session so that proof attempts from earlier scenarios
    # do not merge into this one's prover feedback.
    if os.path.isdir("gnatprove"):
        shutil.rmtree("gnatprove")
    print(f"feedback: {label}")
    prove_all(
        prover=provers,
        steps=1,
        counterexample=False,
        check_counterexamples=False,
        prover_feedback=True,
        opt=[f"--why3-conf={why3_conf}"],
        refiners=default_refiners_no_sort(),
    )
