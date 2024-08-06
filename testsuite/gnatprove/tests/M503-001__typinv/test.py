from test_support import prove_all, gprbuild
from subprocess import call

prove_all()
gprbuild(["-q", "-P", "test.gpr"])
call(["./testinv"])
