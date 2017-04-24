from subprocess import call
from test_support import *
prove_all()
call(["gprbuild", "-q", "-P", "test.gpr"])
