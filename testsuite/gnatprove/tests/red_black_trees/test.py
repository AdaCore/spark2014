from test_support import *

def replay():
    prove_all(procs=0, opt=["--level=2", "--no-axiom-guard", "--no-counterexample"], prover=["cvc4","z3","altergo"], steps=None, vc_timeout=20)
    prove_all(procs=0, opt=["--level=3", "--no-axiom-guard", "--no-counterexample"], prover=["cvc4","z3","altergo"], steps=None, vc_timeout=120)

prove_all(opt=["--replay",
               "--no-axiom-guard",
               "--no-counterexample"],
          steps=None,
          vc_timeout=300,
          prover=["cvc4", "z3", "altergo"])
