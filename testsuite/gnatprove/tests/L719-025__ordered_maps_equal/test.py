from test_support import *

prove_all(steps=1000, prover=["z3", "cvc4", "altergo"])
