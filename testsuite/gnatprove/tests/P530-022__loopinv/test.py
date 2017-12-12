from test_support import *

prove_all(steps=55000, prover=["cvc4", "altergo"], counterexample=False)
