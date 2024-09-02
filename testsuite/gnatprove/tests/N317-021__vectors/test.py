from subprocess import call
from test_support import prove_all, TESTDIR, gprbuild
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

prove_all(steps=8000, sparklib=True)

gprbuild(["-P", "test.gpr", "-q"])
call(["./test_vectors"])
