from test_support import *

prove_all(prover=["cvc4","z3"],opt=["-u","sensfusion6_pack.adb"],counterexample=False)
