from test_support import *
from subprocess import call
import os

os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR
prove_all(steps=2000)
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_arith"])
call(["./test_arith64"])
