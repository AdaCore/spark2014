from test_support import *

prove_all (prover=["z3"], opt=["--z3-counterexample", "--steps=10000"])
check_counterexamples()
