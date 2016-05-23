from test_support import *
from subprocess import call
from gnatpython.env import putenv

putenv("SPARK_LEMMAS_OBJECT_DIR", TESTDIR)
prove_all()
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_arith"])
