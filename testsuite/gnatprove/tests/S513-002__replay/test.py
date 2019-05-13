from test_support import *

prove_all(opt=["--level=4", "--limit-subp=binary_trees.adb:10", "--no-axiom-guard", "--no-counterexample"])
print "--------------------------------------"
prove_all(opt=["--limit-subp=binary_trees.adb:10", "--no-axiom-guard", "--no-counterexample"], replay=True)
