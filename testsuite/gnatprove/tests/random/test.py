from test_support import *

# Prove RTE
prove_all(no_fail=True, steps=6000)

# Execute test program
Run(["gprbuild", "-P", "test.gpr"])
process = Run(["./main"])
print process.out
