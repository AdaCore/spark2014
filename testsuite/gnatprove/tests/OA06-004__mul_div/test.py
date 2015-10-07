from test_support import *

gnatprove(opt=["-P","test.gpr","--prover=cvc4,alt-ergo,z3","--report=all"])
