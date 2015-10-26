from test_support import *

prove_all(prover=["cvc4","altergo"],opt=["-P","test.gpr"], steps=290)
