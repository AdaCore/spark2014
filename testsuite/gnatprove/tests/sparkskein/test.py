from test_support import *

prove_all(prover=["cvc4", "altergo", "z3"],procs=4,steps=0,vc_timeout=120)
