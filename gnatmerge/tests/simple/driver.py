
import readers
from merges import *
from tools import (gnatprove, gnattest)

m = Merge()

subp = m.new_entity("SUBPROGRAM")
s    = subp.states

proofs = gnatprove.GNATprove(subp)
tests  = gnattest.GNATtest(subp)
ok     = s.name_or("OK", {proofs.ok, tests.ok})

# Load tools results

tests.run("contracts.gpr")
proofs.run("contracts.gpr")
m.loads("program.json")

# Output results

g = m.new_goal("OK", subp, ok)

g.print_errors(verbose=True)
