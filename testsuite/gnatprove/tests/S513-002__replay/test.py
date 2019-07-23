from test_support import *

prove_all(opt=["--level=4", "--no-axiom-guard", "--no-counterexample"])
print "--------------------------------------"
prove_all(opt=["--no-axiom-guard", "--no-counterexample"], replay=True)
