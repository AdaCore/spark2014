from test_support import check_counterexamples, prove_all

prove_all(prover=["cvc5"])
check_counterexamples()
