from test_support import *

# Alt-Ergo does not contribute here, so to save time we do not include it
# in the run.

def replay():
    prove_all(procs=0, opt=["--level=2", "--no-axiom-guard", "--no-counterexample"], prover=["cvc4","z3"], steps=None, vc_timeout=20)
    prove_all(procs=0, opt=["--level=3", "--no-axiom-guard", "--no-counterexample"], prover=["cvc4","z3"], steps=None, vc_timeout=60)

prove_all(opt=["--replay",
               "--no-axiom-guard",
               "--no-counterexample"],
          procs=4,
          steps=None,
          vc_timeout=120,
          prover=["cvc4", "z3"])
