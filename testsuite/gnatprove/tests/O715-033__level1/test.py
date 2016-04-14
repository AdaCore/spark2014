from test_support import *
print ""
print "At level 1"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "-j8", "--report=all", "--level=1", "--timeout=auto", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "-j8", "--report=all", "--prover=cvc4,z3,altergo", "--steps=100", "--timeout=1", "--no-counterexample"])
