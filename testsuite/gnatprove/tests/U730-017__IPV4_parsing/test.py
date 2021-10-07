from test_support import *

contains_manual_proof = False

def replay():
    prove_all(level=2,
              prover=["z3", "cvc4", "alt-ergo"],
              procs=10,
              steps=0,
              counterexample=False)

if __name__ == "__main__":
    prove_all(replay=True, no_fail=True, counterexample=False)
