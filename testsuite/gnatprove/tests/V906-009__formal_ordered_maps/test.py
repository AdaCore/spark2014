from subprocess import call
from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

def replay():
    prove_all (level=1, sparklib=True)

if __name__ == "__main__":
    prove_all(replay=True, sparklib=True)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./test"])
