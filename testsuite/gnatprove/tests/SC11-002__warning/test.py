from subprocess import call
from test_support import prove_all

prove_all(sparklib=True)
call(["gprbuild", "-P", "test.gpr", "-q", "-c", "cont.ads"])
