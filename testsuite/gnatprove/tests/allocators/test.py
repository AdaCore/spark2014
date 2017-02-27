from test_support import *

prove_all(level=4,
          steps=None,
          prover=["cvc4", "z3"],
          no_fail=True,
          opt=["-u",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
