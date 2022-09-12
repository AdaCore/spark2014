from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR
prove_all(steps=20000, report="all", sparklib=True)
