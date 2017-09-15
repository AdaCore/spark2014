from test_support import *
prove_all(steps=70000, prover=["z3"], codepeer=True)

# This should have no_fail. CVC4 can discharge the remaining VC easily (to
# be done in Q817-011).
