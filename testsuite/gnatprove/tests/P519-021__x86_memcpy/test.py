# All VCs here are provable in theory, but there are various encoding
# issues making these very difficult problems.

from test_support import *
prove_all(prover=["cvc4"],
          opt=["--no-axiom-guard"],
          counterexample=False)
