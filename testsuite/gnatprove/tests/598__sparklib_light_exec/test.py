from subprocess import call
from test_support import gprbuild, create_sparklib

if __name__ == "__main__":
    create_sparklib(sparklib_bodymode=True)
    gprbuild(["-q", "-P", "test.gpr"])
    print("the following execution should raise an Assertion failure")
    call(["./main"])
