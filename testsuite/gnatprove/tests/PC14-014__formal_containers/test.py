from subprocess import call
from test_support import *

prove_all(steps=1800, prover=["z3"], opt=["--no-axiom-guard"])

call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./run_tests"])
