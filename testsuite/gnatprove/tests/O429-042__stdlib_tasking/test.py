# disable z3 because of platform differences
from test_support import *
prove_all(prover=["cvc4"])
