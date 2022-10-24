from subprocess import call
from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

if __name__ == "__main__":
    prove_all(sparklib=True)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./obj/test"])