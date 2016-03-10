from test_support import *

# Run without flow analysis due to bug in P226-043
prove_all(opt=["--dbg-proof-only", "--proof=progressive"], steps=500)
