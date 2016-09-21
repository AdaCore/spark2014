from test_support import *
# Z3 has problem between mac and linux arch
prove_all(steps = 300, prover = ["cvc4"], codepeer=True)
