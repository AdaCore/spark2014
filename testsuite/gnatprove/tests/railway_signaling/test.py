from test_support import *

# Test was fully proved with 20s timeout, --proof=per_path and a combination
# of provers. Currently, 4 out of 5 unproved assertions are still not proved
# with 10.000 steps and 120s timeout, with --prover=cvc4,altergo,z3 and
# --proof=per_path. This is likely related to the changes in how arrays are
# handled in provers now, to be investigated.

prove_all(steps=570)
