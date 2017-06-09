from test_support import *

prove_all(steps=20000,
          prover=["cvc4", "z3", "alt-ergo"],
          no_fail=True,
          opt=["--no-axiom-guard",
               "-u",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
