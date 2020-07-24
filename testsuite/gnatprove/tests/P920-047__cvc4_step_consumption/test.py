from test_support import *

# Customer reported crash with 100k steps, with 300k steps cvc4 proves
# everything.
prove_all(steps=100000,
          prover=["cvc4_cbqi,z3,altergo"],
          opt=["--why3-conf=why3.conf"],
          counterexample=False)
