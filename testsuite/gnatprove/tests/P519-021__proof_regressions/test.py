from test_support import *
prove_all(level=5, steps=None, prover=["cvc4", "cvc4_alt", "z3", "altergo"],
          procs=4,
          no_fail=True)
