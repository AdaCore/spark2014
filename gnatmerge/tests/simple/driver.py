
from internal import sets
import readers
from internal.attributes import lattices
from internal.attributes import lattice_ops

from tools import *

# Build sketch of inputs

m = sets.Objects()

# subp = new_entity("SUBPROGRAM")
subp = m.new_object("SUBPROGRAMS")
subp.new_attribute(slocs())

# subp = new_entity("VC")
# ...then will disappear when new_child is implemented
vcs = m.new_object("VCS")
vcs.new_attribute(slocs())

# Decorate sketch with the spec of results

# vc = subp.new_child("VC", inherits=proved)
vcs.new_arrow("SUBPROGRAM", lattice_ops.Inclusion(lattice=slocs(),
                                                  object=subp))
subp.new_arrow("STATUS", lattice_ops.Join(lattice=tristate(),
                                          subobject=vcs,
                                          in_object_key="SUBPROGRAM"))
# ...move status attribute down...
vcs.new_attribute(tristate())


# Instanciate sketch from inputs
# ...deduced from command line

vcs.load(readers.ErrorListing("VC", "proofs.out"))
m.loads("program.json")

# Output results

# set_goal(ok)

for i in subp.content():
    print i + " - STATUS : " + str(subp.follow("STATUS", i))

for i in vcs.content():
    print i + " - SUBPROGRAM : " + str(vcs.follow("SUBPROGRAM", i))
