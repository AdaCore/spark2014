from test_support import *

prove_all(prover=["cvc4"],opt=["-XMODE=Analyze"],steps=5700, codepeer=True)
