from test_support import check_counterexamples, prove_all

prove_all(prover=["z3"], opt=["--z3-counterexample", "--steps=10000"])
check_counterexamples()
