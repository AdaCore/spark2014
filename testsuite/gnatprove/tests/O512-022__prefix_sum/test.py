from test_support import *

contains_manual_proof = False

def replay():
    prove_all(level=4,
              procs=0,
              counterexample=False,
              opt=["--no-axiom-guard",
                   "-u",
                   "prefixsum.adb",
                   "prefixsum_expanded.adb",
                   "prefixsum_general.adb"])

prove_all(opt=["--replay",
               "--no-axiom-guard",
               "-u",
               "prefixsum.adb",
               "prefixsum_expanded.adb",
               "prefixsum_general.adb"],
          counterexample=False)
