
import sets
import attributes.lattices
import attributes.lattice_ops

# Build attribute domains

lines = attributes.lattices.RangeAttribute( attributes.lattices.Sloc,
                                            "SLOCS", "LOW", "HIGH")
status = attributes.lattices.PartialOrderAttribute("STATUS",
                                                   {"OK", "KO", "UNKNOWN"})
status.assume_stronger("UNKNOWN", "KO")
status.assume_stronger("UNKNOWN", "OK")

# Build sketch of inputs

m = sets.Objects()

vcs = m.new_object("VCS")
vcs.new_attribute(lines)
vcs.new_attribute(status)

subp = m.new_object("SUBPROGRAMS")
subp.new_attribute(lines)

# Decorate sketch with the spec of results

vcs.new_arrow("SUBPROGRAM",
              attributes.lattice_ops.Inclusion(lattice=lines, object=subp))
subp.new_arrow("STATUS",
               attributes.lattice_ops.Join(lattice=status,
                                           subobject=vcs,
                                           in_object_key="SUBPROGRAM"))

# Instanciate sketch from inputs

m.loads("proofs.json")
m.loads("program.json")

# Output results

for i in subp.content():
    print i + " - STATUS : " + str(subp.follow("STATUS", i))

for i in vcs.content():
    print i + " - SUBPROGRAM : " + str(vcs.follow("SUBPROGRAM", i))
