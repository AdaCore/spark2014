from test_support import *

prove_all(opt=["-P","test.gpr","--prover=z3,alt-ergo"], steps=290)
