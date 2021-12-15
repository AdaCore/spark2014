from test_support import check_counterexamples, prove_all

prove_all(opt=["--z3-counterexample"])
check_counterexamples()
