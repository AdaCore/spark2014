from test_support import *
print ""
print "At level 4"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=4", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--prover=cvc4,z3,altergo", "--timeout=10", "--proof=progressive", "--no-counterexample"])
