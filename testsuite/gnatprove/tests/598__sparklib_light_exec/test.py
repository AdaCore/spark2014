from subprocess import call
import os

os.environ["SPARKLIB_BODY_MODE"] = "On"

if __name__ == "__main__":
    call(["gprbuild", "-q", "-P", "test.gpr"])
    print("the following execution should raise an Assertion failure")
    call(["./main"])
