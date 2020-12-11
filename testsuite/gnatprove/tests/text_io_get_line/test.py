from test_support import *

# Do not run with Z3 (P212-018) until deterministic on all platforms
prove_all(opt=["--proof=progressive",
               "--no-axiom-guard",
               "--prover=cvc4,altergo",
               "--counterexamples=off"],
          steps=1500)
