from subprocess import call
from test_support import prove_all, gprbuild

contains_manual_proof = False

if __name__ == "__main__":
    prove_all(steps=15000, sparklib=True, sparklib_bodymode=True)

    gprbuild(["-q", "-P", "test.gpr"])
    call(["./obj/test"])
