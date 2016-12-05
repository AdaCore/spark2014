from test_support import *

# Test if all three provers can prove such simple property

prove_all(prover=["alt-ergo"])
clean()
prove_all(prover=["cvc4"])
clean()
prove_all(prover=["z3"])
