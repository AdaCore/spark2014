from test_support import *

prove_all(prover=["z3"],opt=["-u","sensfusion6_pack.adb"],counterexample=False)
