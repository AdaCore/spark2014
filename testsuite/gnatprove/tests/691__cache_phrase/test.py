import os
from shutil import rmtree

from test_support import gnatprove

LOCALTMP = os.path.abspath("localtmp")
SOURCE = "test.adb"
ASSERTION = "   pragma Assert (Z = X + Y);"


def run_once(extra_opt=None):
    opt = [
        "-P",
        "test.gpr",
        "--mode=prove",
        "--report=provers",
        "--output=oneline",
        "--quiet",
        "--prover=cvc5",
        "--counterexamples=off",
        "--check-counterexamples=off",
    ]
    if extra_opt:
        opt.extend(extra_opt)
    gnatprove(opt=opt, cache_allowed=False)


def add_assertion():
    with open(SOURCE, encoding="utf-8") as source_file:
        lines = source_file.read().splitlines()

    end_index = lines.index("end Test;")
    if ASSERTION not in lines:
        lines.insert(end_index, ASSERTION)

    with open(SOURCE, "w", encoding="utf-8") as source_file:
        source_file.write("\n".join(lines) + "\n")


print("=== first run ===")
run_once()

add_assertion()

print("=== second run ===")
run_once()

rmtree("gnatprove")
os.makedirs(LOCALTMP, exist_ok=True)

print("=== third run ===")
run_once([f"--memcached-server=file:{LOCALTMP}"])

rmtree("gnatprove")

print("=== fourth run ===")
run_once([f"--memcached-server=file:{LOCALTMP}"])
