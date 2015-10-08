from test_support import *

# Z3 and Alt-ergo proof all except two VCs in several seconds, but only
# with --steps limit higher than the default. CVC4 is excluded from the
# --prover list, becasue is does not prove these two VCs, yet needs about
# 2 minutes before it gives up.
prove_all(opt=["--prover=z3,alt-ergo"], steps=8000)
