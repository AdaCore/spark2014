from test_support import *

# the test should be run with no step limit but it is too long
# this test is a candidate to be a "large" test

# This should be fully proven (no_fail=True) but sadly we're affected by
# a CVC4 regression (bug 743)

prove_all(level=4,
          steps=None,
          prover=["z3", "cvc4"],
          counterexample=False,
          opt=["--dbg-proof-only", "-u",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
