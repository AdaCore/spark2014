from test_support import verify_counterexamples, prove_all

prove_all(prover=["z3"], opt=["--z3-counterexample", "--steps=10000"])
verify_counterexamples()
