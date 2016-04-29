# disable z3 for cross-platform stability
from test_support import *

prove_all(steps=2100, opt=["--report=provers"], prover=["cvc4"])
