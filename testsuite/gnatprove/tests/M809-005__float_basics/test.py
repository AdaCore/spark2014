from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=10, counterexample=False, steps=10000)

if __name__ == "__main__":
    prove_all(replay=True)
