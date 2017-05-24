from test_support import *

def replay():
    prove_all(procs=10, counterexample=False)

prove_all(opt=["--replay"])
