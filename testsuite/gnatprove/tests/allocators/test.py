from test_support import *

# We should remove --dbg-proof-only once OC14-044 is fixed
prove_all(vc_timeout=120, steps=0, \
          opt=["--dbg-proof-only", "-u", "simple_allocator.adb", "list_allocator.adb"])
