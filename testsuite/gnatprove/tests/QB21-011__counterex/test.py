from test_support import check_counterexamples, prove_all

prove_all(opt=["--proof=per_path"])
check_counterexamples()
