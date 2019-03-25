from test_support import *

contains_manual_proof = False

def replay():
    prove_all(opt=["--no-axiom-guard"],
              prover=["cvc4", "z3", "altergo"],
              procs=10,
              steps=5000)

prove_all(opt=["--no-axiom-guard"],
          prover=["cvc4", "z3", "altergo"],
          replay=True)
