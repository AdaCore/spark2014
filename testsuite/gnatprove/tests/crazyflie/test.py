from test_support import *

prove_all(prover=["cvc4","altergo"],opt=["-XMODE=Analyze"],steps=5000)
