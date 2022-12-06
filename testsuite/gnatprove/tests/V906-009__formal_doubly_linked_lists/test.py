from subprocess import call
from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR


def replay():
    prove_all(level=3, procs=0)


if __name__ == "__main__":
    prove_all(replay=True)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./obj/test"])
