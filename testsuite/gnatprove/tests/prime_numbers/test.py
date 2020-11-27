from test_support import *

contains_manual_proof = False

def replay():
    prove_all(level=2, procs=0, counterexample=False)

if __name__ == "__main__":
    prove_all(replay=True, counterexample=False)
