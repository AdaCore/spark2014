
import readers
from merges import *
from tools import (gnatprove, gnattest, asistree)

m = Merge()

subp = m.new_entity("SUBPROGRAM")
s    = subp.states

proofs = gnatprove.GNATprove(subp)
tests  = gnattest.GNATtest(subp)
ok     = s.name_or("OK", {proofs.ok, tests.ok})

at = asistree.AsisTree(subp, ["A_Procedure_Declaration",
                              "A_Procedure_Body_Declaration",
                              "A_Null_Procedure_Declaration",
                              "A_Procedure_Body_Stub",
                              "A_Function_Body_Stub",
                              "A_Function_Declaration",
                              "A_Function_Body_Declaration",
                              "An_Expression_Function_Declaration"])
# Load tools results

tests.run()
proofs.run()
at.run()

# Output results

g = m.new_goal("OK", subp, ok)
g.print_errors(verbose=True)
