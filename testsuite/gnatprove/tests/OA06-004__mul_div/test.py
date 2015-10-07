from test_support import *

prove_all(opt=["-P","test.gpr","--prover=alt-ergo,z3"],steps=5000)
