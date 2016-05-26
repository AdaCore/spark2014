# disable z3 for cross-platform stability
from test_support import *

prove_all(opt=["--report=provers"], prover=["cvc4"])
