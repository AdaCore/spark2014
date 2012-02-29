
import json
import topoi
import sketches

with open("program.json") as f:
    program = json.loads(f.read())
with open("proofs.json") as f:
    proofs = json.loads(f.read())
with open("tests.json") as f:
    tests = json.loads(f.read())

partial_order = sketches.PartialOrder({"PROVED", "TESTED", "OK", "SUBPROGRAM"})
partial_order.assume_stronger("PROVED", "OK")
partial_order.assume_stronger("TESTED", "OK")
partial_order.assume_stronger("OK", "SUBPROGRAM")

classifier = topoi.Classifier(partial_order)

o = topoi.Subobjects(classifier, program)
p = o.subobject(proofs)
t = o.subobject(tests)
j = o.join(p, t)

# test the result:

for prog in ["P0", "P1", "P3", "P4"]:
    assert ("OK" in j[prog])

for prog in ["P2", "P5", "P6"]:
    assert (not ("OK" in j[prog]))
