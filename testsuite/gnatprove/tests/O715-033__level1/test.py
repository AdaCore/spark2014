from test_support import *
print ""
print "At level 1"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=1", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--prover=cvc4,z3,altergo", "--timeout=1", "--no-counterexample"])
