from test_support import *

contains_manual_proof = False

def replay():
    prove_all(level=2,
              procs=10,
              steps=0)

if __name__ == "__main__":
    prove_all(replay=True, no_fail=True)
