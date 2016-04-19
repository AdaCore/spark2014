from test_support import *
print ""
print "At level 4"
print "----------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=4", "--timeout=auto", "--no-counterexample"])

print ""
print "Equivalent switches"
print "-------------------"
gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--prover=cvc4,z3,altergo", "--steps=10000", "--timeout=60", "--proof=progressive", "--no-counterexample"])
