from test_support import verify_counterexamples, prove_all

prove_all(prover=["cvc5"])
verify_counterexamples()
