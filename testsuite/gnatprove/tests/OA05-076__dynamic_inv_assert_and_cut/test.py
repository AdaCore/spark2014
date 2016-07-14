from test_support import *

prove_all(level=1, steps=None,
          counterexample=False,
          prover=["cvc4"],
          procs=4)
