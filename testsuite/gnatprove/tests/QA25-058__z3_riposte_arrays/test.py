from test_support import *

prove_all (opt=["--z3-counterexample"])
check_counterexamples()
