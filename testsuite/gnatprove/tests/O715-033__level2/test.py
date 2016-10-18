from test_support import *
print ""
print "At level 2"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=2", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--prover=cvc4,z3,altergo", "--timeout=5", "--no-counterexample"])
