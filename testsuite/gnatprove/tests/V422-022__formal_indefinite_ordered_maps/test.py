from subprocess import call
from test_support import prove_all, gprbuild
import os

contains_manual_proof = False
os.environ["SPARKLIB_BODY_MODE"] = "On"

# Counterexample generation does not seem to consume the steps correctly on
# this test.

if __name__ == "__main__":
    prove_all(counterexample=False, steps=35000, sparklib=True)

    gprbuild(["-q", "-P", "test.gpr"])
    call(["./obj/test"])
