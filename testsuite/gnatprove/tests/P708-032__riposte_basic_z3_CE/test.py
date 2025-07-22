from test_support import verify_counterexamples, prove_all

prove_all(opt=["--z3-counterexample"])
verify_counterexamples()
