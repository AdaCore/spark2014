import os
from subprocess import call
from test_support import gprbuild

os.environ["SPARKLIB_BODY_MODE"] = "On"

if __name__ == "__main__":
    gprbuild(["-q", "-P", "test.gpr"])
    print("the following execution should raise an Assertion failure")
    call(["./main"])
