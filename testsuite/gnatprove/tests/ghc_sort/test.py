from test_support import *

contains_manual_proof = False

def replay():
    prove_all(prover=["z3", "cvc4", "altergo"],
              level=2,
              procs=10)

if __name__ == "__main__":
    prove_all(prover=["z3", "cvc4", "altergo"],
              replay=True)
