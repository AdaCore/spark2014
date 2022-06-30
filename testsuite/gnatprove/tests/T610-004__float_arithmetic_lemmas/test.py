from test_support import prove_all, TESTDIR
from subprocess import call
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
prove_all(steps=2000, counterexample=False, sparklib=True)
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_arith"])
call(["./test_arith64"])
