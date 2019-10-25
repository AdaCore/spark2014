from subprocess import call
from test_support import *

prove_all(steps=5000,
          counterexample=False,
          procs=4,
          prover=["z3", "cvc4"],
          opt=["--no-axiom-guard"])

call(["gprbuild", "-q", "-P", "test.gpr"])
call(["./run_tests"])
