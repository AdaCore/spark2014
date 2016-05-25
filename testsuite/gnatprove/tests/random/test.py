from test_support import *

# Prove RTE
prove_all()

# Execute test program
Run(["gprbuild", "-P", "test.gpr"])
process = Run(["./main"])
print process.out
