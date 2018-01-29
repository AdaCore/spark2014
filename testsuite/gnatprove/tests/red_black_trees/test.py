from test_support import *

def replay():
    prove_all(procs=0, opt=["--no-axiom-guard", "--no-counterexample"],
            prover=["cvc4"], steps=100)

prove_all(opt=["--replay",
               "--no-axiom-guard",
               "--no-counterexample"],
          prover=["cvc4"])
