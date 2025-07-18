from test_support import prove_all, TESTDIR, gprbuild
from subprocess import call
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
prove_all(steps=1500, sparklib=True)
gprbuild(["-q", "-P", "test.gpr"])
call(["./test_arith"])
