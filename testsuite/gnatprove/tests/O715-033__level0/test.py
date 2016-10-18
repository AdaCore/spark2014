from test_support import *

print "At level 0"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=0", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--prover=cvc4", "--timeout=1", "--no-counterexample"])
