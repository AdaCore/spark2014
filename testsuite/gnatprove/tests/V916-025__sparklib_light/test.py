from test_support import prove_all
from subprocess import call
import os

os.environ["SPARKLIB_OBJECT_DIR"] = "obj"

call(["gprbuild", "-q", "-P", "test.gpr"])
prove_all(opt=["-U"])
