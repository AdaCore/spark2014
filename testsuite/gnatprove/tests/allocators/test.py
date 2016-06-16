from test_support import *

# the test should be run with no step limit but it is too long
# this test is a candidate to be a "large" test

prove_all(vc_timeout=120, prover=["z3", "cvc4"], counterexample=False, \
          opt=["--dbg-proof-only", "--steps=0", "-u", "simple_allocator.adb", "list_allocator.adb", "list_mod_allocator.adb"])
