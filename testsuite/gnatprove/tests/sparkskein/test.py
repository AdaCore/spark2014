from test_support import *

# Some checks currently require as much as 100.000 steps with CVC4
# currently. This is notoriously high, and might be related to the issue with
# CVC4 reported in O525-023. To be investigated.
prove_all(opt=["--prover=cvc4"],steps=100000,procs=4)

# With --prover=cvc4,z3,altergo --timeout=60 everything is proved except the
# assertion on line 580, which simply repeats the value assigned to constant
# Src_Offset at declaration line 564.
