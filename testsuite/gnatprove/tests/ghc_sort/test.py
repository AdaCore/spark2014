from test_support import *

contains_manual_proof = False

def replay():
    prove_all(prover=["z3", "cvc4", "altergo"],
              procs=10,
              steps=5000)
prove_all(prover=["z3", "cvc4", "altergo"],
          replay=True)
