from subprocess import call
from test_support import prove_all, gprbuild

if __name__ == "__main__":
    prove_all(sparklib=True, steps=11000, sparklib_bodymode=True)

    gprbuild(["-q", "-P", "test.gpr"])
    call(["./obj/test"])
