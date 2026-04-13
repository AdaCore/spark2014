import os
from shutil import rmtree

from test_support import gnatprove

LOCALTMP = os.path.abspath("localtmp")


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


print("=== first run ===")
run_once()

print("=== second run ===")
run_once()

rmtree("gnatprove")
os.makedirs(LOCALTMP, exist_ok=True)

print("=== third run ===")
run_once([f"--memcached-server=file:{LOCALTMP}"])

rmtree("gnatprove")

print("=== fourth run ===")
run_once([f"--memcached-server=file:{LOCALTMP}"])
