from test_support import *

contains_manual_proof = False

def replay():
    prove_all(prover=["cvc4", "z3"],
              procs=0,
              level=4,
              counterexample=False)

prove_all(prover=["cvc4", "z3"], replay=True, counterexample=False)
