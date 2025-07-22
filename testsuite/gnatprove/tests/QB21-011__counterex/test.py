from test_support import verify_counterexamples, prove_all

prove_all(opt=["--proof=per_path"])
verify_counterexamples()
