from test_support import *
# Z3 has problem between mac and linux arch
# counter examples disabled to avoid DIFFs
prove_all(steps = 1000, prover = ["cvc4"], codepeer=True, counterexample=False)
