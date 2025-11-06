from subprocess import call
from test_support import prove_all, gprbuild

# Counterexample generation does not seem to consume the steps correctly on
# this test.

if __name__ == "__main__":
    prove_all(counterexample=False, steps=35000, sparklib=True, sparklib_bodymode=True)

    gprbuild(["-q", "-P", "test.gpr"])
    call(["./obj/test"])
