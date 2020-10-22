from test_support import *

prove_all(opt=["--no-axiom-guard",
               "--proof-warnings",
               "-u",
               "prefixsum.adb",
               "prefixsum_expanded.adb",
               "prefixsum_general.adb"],
          steps=1000,
          counterexample=False)
