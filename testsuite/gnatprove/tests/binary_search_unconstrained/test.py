from test_support import *
prove_all(no_fail=True, opt=["-u", "binary_search.adb"], prover=["altergo"],
        steps=5000)
