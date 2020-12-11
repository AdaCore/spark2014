from test_support import *

prove_all(opt=["--level=4", "--no-axiom-guard", "--counterexamples=off"])
print("--------------------------------------")
prove_all(opt=["--no-axiom-guard", "--counterexamples=off"], replay=True)
