from test_support import prove_all, TESTDIR
from subprocess import call
import os

os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR
prove_all(codepeer=True, steps=1000)
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_arith"])
