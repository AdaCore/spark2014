from test_support import *

prove_all(vc_timeout=120, steps=None, prover=["z3", "cvc4"], counterexample=False, \
          opt=["--dbg-proof-only", "-u", "simple_allocator.adb", "list_allocator.adb"])
