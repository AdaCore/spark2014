from test_support import *

prove_all(steps=10000,
          no_fail=True,
          counterexample=False,
          opt=["--no-axiom-guard",
               "-u",
               "--proof=progressive",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
