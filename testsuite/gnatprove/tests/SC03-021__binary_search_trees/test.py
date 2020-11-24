import glob
from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, level=1, opt=["--no-axiom-guard"])
    prove_all(procs=0, level=4, opt=["--no-axiom-guard"])

if __name__ == "__main__":
    prove_all(replay=True, opt=["--no-axiom-guard"])
