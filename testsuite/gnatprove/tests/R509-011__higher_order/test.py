from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
prove_all(
    no_fail=True,
    prover=["cvc5", "altergo", "z3"],
    steps=16000,
    opt=["-u", "test_higher_order.ads"],
)
