from test_support import *

# Do not run with counterexamples, as on Darwin this takes too much time.
# Do not run with Z3 (P212-018) until deterministic on all platforms.
prove_all(steps = 240, counterexample=False,
          opt=["--prover=cvc4,altergo"])
