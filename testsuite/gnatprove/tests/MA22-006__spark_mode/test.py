from test_support import check_output_file, clean, do_flow, prove_all

do_flow()
check_output_file()
clean()

prove_all(opt=["--report=fail"])
check_output_file()
clean()

prove_all(opt=["--report=fail"])
check_output_file()
clean()

do_flow()
prove_all(opt=["--report=fail"])
check_output_file()
clean()
