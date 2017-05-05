from test_support import *

prove_all(steps=9000,
          prover=["cvc4", "z3"],
          no_fail=True,
          opt=["--no-axiom-guard",
               "-u",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
