from test_support import prove_all, TESTDIR
from subprocess import call, gprbuild
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
prove_all(steps=1000, sparklib=True)
gprbuild(["-q", "-P", "test.gpr"])
call(["./test_arith"])
