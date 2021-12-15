from test_support import prove_all
from subprocess import call

prove_all()
call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./testinv"])
