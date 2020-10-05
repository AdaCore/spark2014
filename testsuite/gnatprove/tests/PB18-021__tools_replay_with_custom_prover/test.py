from test_support import *

contains_manual_proof = False

def replay():
    prove_all(opt=["--why3-conf=why3.conf"], prover=["cvc4_alt"])

if __name__ == "__main__":
    prove_all(opt=["--why3-conf=why3.conf"], prover=[], replay=True)
