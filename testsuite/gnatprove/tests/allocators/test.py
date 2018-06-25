from test_support import *

prove_all(steps=1000000,
          level=4,
          no_fail=True,
          opt=["--no-axiom-guard",
               "-u",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
