from subprocess import call
from test_support import gprbuild, create_sparklib

if __name__ == "__main__":
    create_sparklib()
    gprbuild(["-q", "-P", "test.gpr"], sparklib_bodymode=True)
    print("the following execution should raise an Assertion failure")
    call(["./main"])
