from test_support import *
prove_all(steps=500000,
          prover=["cvc4_cbqi", "cvc4"],
          opt=["--why3-conf=why3.conf"],
          counterexample=False,
          no_fail=True,
          subdue_flow=True)
