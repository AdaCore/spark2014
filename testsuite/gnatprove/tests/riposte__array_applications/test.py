# disable z3 for cross-platform stability
from test_support import *
prove_all(steps=1600, prover=["cvc4"])
