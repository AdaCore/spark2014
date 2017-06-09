from test_support import *

def replay():
    prove_all(opt=["--no-axiom-guard"],
              prover=["cvc4", "z3", "altergo"],
              procs=10,
              steps=5000)

prove_all(no_fail=True,
          opt=["--replay", "--no-axiom-guard"],
          prover=["cvc4", "z3", "altergo"])
