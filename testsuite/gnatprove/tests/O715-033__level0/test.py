from test_support import *

print "At level 0"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "-j8", "--report=all", "--level=0", "--timeout=auto", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "-j8", "--report=all", "--prover=cvc4", "--steps=100", "--timeout=1", "--no-counterexample"])
