from test_support import *
prove_all(prover=["cvc4","z3","alt-ergo"],
          steps=2300,
          counterexample=False)
