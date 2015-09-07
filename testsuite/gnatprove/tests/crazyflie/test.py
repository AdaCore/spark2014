from test_support import *

prove_all(opt=["-XMODE=Analyze","--prover=cvc4,z3,altergo"],steps=1000,procs=8)
