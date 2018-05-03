from test_support import *

# Do not use alt-ergo which seems to be unsound on this test

prove_all(prover=["cvc4", "z3"])
