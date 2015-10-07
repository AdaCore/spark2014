from test_support import *

gnatprove(opt=["-P","test.gpr","--prover=z3,alt-ergo","--report=all"])
