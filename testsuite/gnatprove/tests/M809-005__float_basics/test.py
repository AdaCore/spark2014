from test_support import *

def replay():
    prove_all(procs=10, counterexample=False, prover=["z3","cvc4","altergo"])

prove_all(opt=["--replay"])
