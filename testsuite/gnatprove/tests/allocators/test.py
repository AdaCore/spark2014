from test_support import *

# We should remove --dbg-proof-only once OC14-044 is fixed
prove_all(prover=["cvc4", "z3"], vc_timeout=120, steps=0, procs=4, \
          opt=["--dbg-proof-only", "--proof=progressive", "-u", "simple_allocator.adb", "list_allocator.adb"])
