
import json
import topoi
import sketches

with open("program.json") as f:
    program = json.loads(f.read())
with open("proofs.json") as f:
    proofs = json.loads(f.read())
with open("tests.json") as f:
    tests = json.loads(f.read())

sketch = sketches.FiniteSketch({"PROVED", "TESTED", "OK", "SUBPROGRAM"})
sketch.add_monic("PROVED", "OK")
sketch.add_monic("TESTED", "OK")
sketch.add_monic("OK", "SUBPROGRAM")

print "--------------------------------------------------------------------"
print "BY DOMAIN:"
for elt in sketch.arrows_by_domain:
    print elt
    for arrow in sketch.arrows_by_domain[elt]:
        print " " + sketches.arrow_to_string(arrow)
print "--------------------------------------------------------------------"
print "BY CODOMAIN:"
for elt in sketch.arrows_by_codomain:
    print elt
    for arrow in sketch.arrows_by_codomain[elt]:
        print " " + sketches.arrow_to_string(arrow)

print "--------------------------------------------------------------------"

o = topoi.Realization(sketch, program)
p = o.subobject(proofs)
t = o.subobject(tests)
r = o.subobject({"all" : "OK"})
print o.minimum
print ""
print r
print ""
j = o.join(p, t)
print j
print ""
m = o.meet(p, t)
print m
print ""
i = o.imply(r, j)
print i
print ""

# classifier = topoi.Classifier(partial_order)

# o = topoi.Subobjects(classifier, program)
# p = o.subobject(proofs)
# for i in p:
#     print str(i) + "    :     " + str(p[i])
#t = o.subobject(tests)
#j = o.join(p, t)

# test the result:

#for prog in ["P0", "P1", "P3", "P4"]:
#    assert ("OK" in j[prog])

#for prog in ["P2", "P5", "P6"]:
#    assert (not ("OK" in j[prog]))
