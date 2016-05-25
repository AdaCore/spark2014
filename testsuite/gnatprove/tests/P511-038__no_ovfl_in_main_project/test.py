from test_support import *
from subprocess import call

prove_all(opt=["--report=fail"])
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./check"])
