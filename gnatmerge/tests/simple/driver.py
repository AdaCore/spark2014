
import readers
from tools import *

# Build sketch of inputs

m = Merge()

subp = m.new_entity("SUBPROGRAM")
vcs = subp.new_child("VC", inherits=m.tristate)

vcs.object.load(readers.ErrorListing("VC", "proofs.out"))
m.loads("program.json")

# Output results

# set_goal(ok)

for i in vcs.object.content():
    print i + " - SUBPROGRAM : " + str(vcs.object.follow("SUBPROGRAM", i))

for i in subp.object.content():
    print i + " - STATUS : " + str(subp.object.follow("STATUS", i))

