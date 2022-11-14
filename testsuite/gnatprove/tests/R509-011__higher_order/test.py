from subprocess import call
from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
# disable no_fail, see VB03-004
prove_all(
    no_fail=False,
    prover=["cvc5", "altergo", "z3"],
    steps=150000,
    opt=["-u", "test_higher_order.ads"],
)
call(["gprbuild", "-q", "-P", "test.gpr"])
