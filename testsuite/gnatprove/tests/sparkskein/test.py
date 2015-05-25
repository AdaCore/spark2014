from test_support import *

# Some checks currently require as much as 100.000 steps with CVC4
# currently. This is notoriously high, and might be related to the issue with
# CVC4 reported in O525-023. To be investigated.
prove_all(opt=["--prover=cvc4"],steps=100000,procs=4)
