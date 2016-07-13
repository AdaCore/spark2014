from test_support import *

prove_all(level=4,
          steps=None,
          prover=["z3", "cvc4"],
          no_fail=True,
          opt=["-u",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
