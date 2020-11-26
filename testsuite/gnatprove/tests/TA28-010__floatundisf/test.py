from test_support import *

prove_all(prover=["z3", "cvc4", "altergo", "colibri"], counterexample=False)
