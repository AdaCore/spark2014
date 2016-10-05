from test_support import *
prove_all(prover=["cvc4","z3","alt-ergo"],
          steps=1,
          no_output=True,
          counterexample=False)
prove_all(prover=["alt-ergo"],
          steps=2300,
          no_output=True,
          counterexample=False)
prove_all(prover=["cvc4"],
          steps=2300,
          no_fail=True,
          counterexample=False)
