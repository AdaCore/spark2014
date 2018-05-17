from test_support import *

prove_all(prover=["cvc4","z3"],
          procs=2,
          opt=["-u","sensfusion6_pack.adb","--no-axiom-guard"],
          counterexample=False)
