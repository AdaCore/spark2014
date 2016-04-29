from test_support import *
from subprocess import call
from gnatpython.env import putenv

putenv("SPARK_LEMMAS_OBJECT_DIR", ".")
prove_all(steps=1000)
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_arith"])
