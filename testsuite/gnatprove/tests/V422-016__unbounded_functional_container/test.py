from subprocess import call
from test_support import prove_all
import os

os.environ["SPARKLIB_BODY_MODE"] = "On"

if __name__ == "__main__":
    prove_all(steps=1300, sparklib=True)

    call(["gprbuild", "-q", "-P", "test.gpr"])
    call(["./obj/infinite_sequence"])
