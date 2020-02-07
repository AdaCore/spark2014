from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, opt=["--level=2", "--no-axiom-guard", "--no-counterexample"], steps=None)

prove_all(opt=["--no-axiom-guard",
               "--no-counterexample"],
          replay=True)
