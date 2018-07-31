from test_support import *
from subprocess import call
from gnatpython.env import putenv

putenv("SPARK_LEMMAS_OBJECT_DIR", TESTDIR)
call(["gprbuild", "-q", "-U", "-P", "test.gpr"])
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./test_lemmas"])
