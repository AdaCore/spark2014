from subprocess import call
from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

call(["gprbuild", "-q", "-c", "cont.ads"])
prove_all(sparklib=True,)
