from test_support import *
prove_all(prover=["cvc4","alt-ergo"],
          steps=500,
          counterexample=False)
