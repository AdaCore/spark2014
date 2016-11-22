from test_support import *

# The idea of this test is to exercise FP support.
#
# To best exercise the floating point support we use Z3 where we strip out
# all quantifiers.
#
# Once CVC4 supports floats we will include it here too.
prove_all(prover=["z3_noquant,altergo"], steps=5000, counterexample=False)
