from subprocess import call
from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

# Counterexample generation does not seem to consume the steps correctly on
# this test.

if __name__ == "__main__":
    prove_all(counterexample=False, steps=20000)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./obj/test"])
