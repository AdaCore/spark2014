from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, opt=["--no-axiom-guard", "--no-counterexample"], level=2)

prove_all(opt=["--no-axiom-guard",
               "--no-counterexample"],
          replay=True)
