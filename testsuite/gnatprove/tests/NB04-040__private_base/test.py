from test_support import *

# Use debug flag until NC15-008 is fixed, to avoid crash in generation of globals by flow
prove_all(opt=["--dbg-proof-only"])
