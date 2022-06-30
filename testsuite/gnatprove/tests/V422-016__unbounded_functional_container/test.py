from subprocess import call
from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

if __name__ == "__main__":
    prove_all(steps=1282, sparklib=True)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./infinite_sequence"])

