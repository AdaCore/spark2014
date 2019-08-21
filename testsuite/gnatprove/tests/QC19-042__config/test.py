from test_support import *
prove_all(opt=["--why3-conf=no_main_section.conf", "--prover=altergo2"], cache_allowed=False)
prove_all(opt=["--why3-conf=wrong_driver_file.conf", "--prover=altergo2"], cache_allowed=False)
prove_all(opt=["--why3-conf=redefine_predefined.conf", "--prover=altergo2,cvc4"], cache_allowed=False)
