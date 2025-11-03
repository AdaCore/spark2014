from subprocess import call
from test_support import prove_all, gprbuild
import os

os.environ["SPARKLIB_BODY_MODE"] = "On"

if __name__ == "__main__":
    prove_all(steps=2000, sparklib=True)

    gprbuild(["-q", "-P", "test.gpr"])
    call(["./obj/test"])
