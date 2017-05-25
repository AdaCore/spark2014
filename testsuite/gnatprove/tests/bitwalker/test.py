from test_support import *

def replay():
    prove_all(opt=["--why3-conf=why3.conf", "--no-axiom-guard"],
              prover=["cvc4", "cvc4_alt", "z3", "altergo"],
              procs=10,
              steps=5000)

# We use a different configuration for CVC4 here to fully complete the
# proof. We keep having issues with bitvector-heavy code, and a CBQI and a
# different decision heuristic is quite useful here. However, its much
# worse overall so we don't have it enabled by default.
prove_all(no_fail=True,
          opt=["--why3-conf=why3.conf", "--replay", "--no-axiom-guard"],
          prover=["cvc4", "cvc4_alt", "z3", "altergo"])
