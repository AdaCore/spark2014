from test_support import *

prove_all(steps=50000, prover=["cvc4"], counterexample=False)
