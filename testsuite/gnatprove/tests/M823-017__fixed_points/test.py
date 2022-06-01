from test_support import prove_all

prove_all(prover=["altergo", "cvc5"], opt=["-u", "binary_fixed.adb"], steps=3600)
prove_all(prover=["altergo", "cvc5"], opt=["-u", "decimal_fixed.adb"], steps=3600)
prove_all(prover=["altergo", "cvc5"], opt=["-u", "ordinary_fixed.adb"], steps=3600)
prove_all(opt=["-u", "dynamic_fixed.adb"])
prove_all(opt=["-u", "unsupported.adb"])
