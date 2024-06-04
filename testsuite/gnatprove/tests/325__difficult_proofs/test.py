from test_support import prove_all, check_output_file

prove_all(prover=["cvc5"], steps=0, vc_timeout=30)
check_output_file()
