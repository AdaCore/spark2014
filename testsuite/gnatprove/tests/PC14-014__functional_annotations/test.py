from test_support import *

prove_all(no_fail=True, steps=4000, prover=["z3", "cvc4"])
