from test_support import *
prove_all(no_fail=True, prover=["cvc4", "z3"], opt=["-u", "lexer.adb"])
