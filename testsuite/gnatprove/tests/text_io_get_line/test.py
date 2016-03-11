from test_support import *

# Run without flow analysis due to bug in P226-043
# Do not run with Z3 (P212-018) until deterministic on all platforms
prove_all(opt=["--dbg-proof-only",
               "--proof=progressive",
               "--prover=cvc4,altergo"],
          steps=500)
