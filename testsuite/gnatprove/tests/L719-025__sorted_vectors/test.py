# disable z3 for cross-platform stability
from test_support import *

prove_all(steps=2000, prover=["cvc4"])
