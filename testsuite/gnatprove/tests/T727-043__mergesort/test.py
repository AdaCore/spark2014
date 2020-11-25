from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, level=4)

if __name__ == "__main__":
    prove_all(replay=True)

# Ideally this test should have no fail
