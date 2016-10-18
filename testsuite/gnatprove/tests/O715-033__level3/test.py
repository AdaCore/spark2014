from test_support import *
print ""
print "At level 3"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=3", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--prover=cvc4,z3,altergo", "--timeout=5", "--proof=progressive", "--no-counterexample"])
