from test_support import *

def replay():
    prove_all(procs=0, opt=["--level=2", "--no-axiom-guard", "--no-counterexample"], prover=["z3", "cvc4"], steps=None, vc_timeout=10)
    prove_all(procs=0, opt=["--level=4", "--no-axiom-guard", "--no-counterexample"], prover=["cvc4","z3"], steps=None, vc_timeout=60)

prove_all(
          opt=["--replay",
               "--no-axiom-guard",
               "--no-counterexample"],
          prover=["cvc4", "z3"])
