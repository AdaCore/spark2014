from test_support import *
import os

# At level 2
sys.stdout = open('result1', 'w')
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=2", "--no-counterexample"])

# Cleanup
clean()

# Equivalent switches
sys.stdout = open('result2', 'w')
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--prover=cvc4,z3,altergo", "--timeout=5", "--steps=0", "--memlimit=1000", "--no-counterexample"])

# Diff between the two
sys.stdout = sys.__stdout__
os.system("diff result1 result2")
