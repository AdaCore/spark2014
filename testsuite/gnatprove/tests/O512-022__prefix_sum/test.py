from test_support import *

prove_all(opt=["--no-axiom-guard",
               "-u",
               "prefixsum.adb",
               "prefixsum_expanded.adb",
               "prefixsum_general.adb"],
          counterexample=False)
