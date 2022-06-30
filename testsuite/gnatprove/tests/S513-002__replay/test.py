from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

prove_all(opt=["--level=4", "--no-axiom-guard", "--counterexamples=off"], sparklib=True)
print("--------------------------------------")
prove_all(opt=["--no-axiom-guard", "--counterexamples=off"], replay=True, sparklib=True)
