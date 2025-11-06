from subprocess import call
from test_support import prove_all, gprbuild

if __name__ == "__main__":
    prove_all(steps=1, sparklib=True, sparklib_bodymode=True)
    gprbuild(["-q", "-P", "test.gpr"])
    call(["./test"])
