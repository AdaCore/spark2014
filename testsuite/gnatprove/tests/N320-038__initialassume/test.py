from test_support import check_output_file, prove_all

prove_all(opt=["--assumptions"])
check_output_file(sort=True)
