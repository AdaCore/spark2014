from test_support import *
print ""
print "At level 2"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "-j8", "--report=all", "--level=2", "--timeout=auto", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "-j8", "--report=all", "--prover=cvc4,z3,altergo", "--steps=1000", "--timeout=10", "--no-counterexample"])
