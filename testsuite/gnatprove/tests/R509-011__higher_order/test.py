from test_support import prove_all, TESTDIR
import os

os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR
prove_all(
    no_fail=True,
    prover=["cvc4", "altergo", "z3"],
    steps=1000000,
    opt=["-u", "test_higher_order.ads"],
)
