from test_support import *

prove_all(vc_timeout=120, steps=100000, prover=["cvc4"], \
          opt=["--dbg-proof-only", "-u", "simple_allocator.adb", "list_allocator.adb"])
