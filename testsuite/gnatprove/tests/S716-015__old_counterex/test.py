from test_support import check_counterexamples, prove_all

prove_all(prover=["cvc4"])
check_counterexamples()
