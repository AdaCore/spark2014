from test_support import *

prove_all(opt=["-XMODE=Analyze","--prover=cvc4,altergo"],steps=5000)
