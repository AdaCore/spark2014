from test_support import *

contains_manual_proof = False

def replay():
    prove_all(prover=["cvc4", "altergo", "z3"], no_fail=True, procs=0, steps=0, vc_timeout=240)

if __name__ == "__main__":
    prove_all(procs=4, replay=True, no_fail=True)
