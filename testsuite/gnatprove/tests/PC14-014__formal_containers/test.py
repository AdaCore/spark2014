from subprocess import call
from test_support import *

prove_all(steps=300, prover=["z3"])

call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./run_tests"])
