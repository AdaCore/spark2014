from subprocess import call
import os
from test_support import TESTDIR

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
call(["gprbuild", "-q", "-U", "-P", "test.gpr"])
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_lemmas"])
