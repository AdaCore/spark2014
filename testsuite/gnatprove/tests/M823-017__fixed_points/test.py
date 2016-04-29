# disable z3 for cross-platform stability
from test_support import *
prove_all(prover=["cvc4"], opt=["-u","binary_fixed.adb"], steps=3600)
prove_all(prover=["cvc4"], opt=["-u","decimal_fixed.adb"], steps=3600)
prove_all(prover=["cvc4"], opt=["-u","dynamic_fixed.adb"])
prove_all(prover=["cvc4"], opt=["-u","unsupported.adb"])
