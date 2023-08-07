from subprocess import call
from test_support import prove_all
import os

contains_manual_proof = False
os.environ["SPARKLIB_BODY_MODE"] = "On"


def replay():
    prove_all(level=3, procs=0, sparklib=True)


if __name__ == "__main__":
    prove_all(replay=True, sparklib=True)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./obj/test"])
