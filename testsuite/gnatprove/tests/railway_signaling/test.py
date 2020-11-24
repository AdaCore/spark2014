from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, level=1, counterexample=False)
    prove_all(procs=0, level=4, counterexample=False)

if __name__ == "__main__":
    prove_all(replay=True, level=1, counterexample=False)
