
import readers
from merges import *

print
print "**********"
print "* Test 1 *"
print "**********"
print

m = Merge()

subp = m.new_entity("SUBPROGRAM")
s    = subp.states

proved    = s.new_value("PROVED")
not_p     = s.new_value("NOT PROVED")
partial_p = s.name_and("PARTIALLY PROVED", {proved, not_p})

vcs = subp.new_input(reader=readers.ErrorListing("VC"),
                     union_name=subp.status_attr_id(),
                     inclusion=subp.slocs,
                     maps={"OK" : proved,
                           "KO" : not_p})
vcs.load("obj/gnatprove.mrg")
m.loads("program.json")

# Output results

for i in vcs.object.content():
    print i + " - SUBPROGRAM : " + str(vcs.object.follow("SUBPROGRAM", i))

for name in ["VC.STATUS", "SUBPROGRAM.STATUS"]:
    for i in vcs.object.content():
        print i + " - " + name + " : " + str(vcs.object.follow(name, i))

for i in subp.object.content():
    name = "SUBPROGRAM.STATUS"
    print i + " - " + name + " : " + str(subp.object.follow(name, i))

print
print "**********"
print "* Test 2 *"
print "**********"
print

m = Merge()

subp = m.new_entity("SUBPROGRAM")
s    = subp.states

proved    = s.new_value("PROVED")
not_p     = s.new_value("NOT PROVED")
partial_p = s.name_and("PARTIALLY PROVED", {proved, not_p})

vcs = subp.new_input(reader=readers.ErrorListing("VC"),
                     union_name=subp.status_attr_id(),
                     inclusion=subp.slocs,
                     maps={"OK" : proved})

vcs.load("gnatprove2.out")
m.loads("program.json")

# Output results

for name in ["SUBPROGRAM.STATUS"]:
    for i in vcs.object.content():
        print i + " - " + name + " : " + str(vcs.object.follow(name, i))

for i in subp.object.content():
    name = "SUBPROGRAM.STATUS"
    print i + " - " + name + " : " + str(subp.object.follow(name, i))

print
print "**********"
print "* Test 3 *"
print "**********"
print

m = Merge()

subp = m.new_entity("SUBPROGRAM")
s    = subp.states

proved    = s.new_value("PROVED")
not_p     = s.new_value("NOT PROVED")
partial_p = s.name_and("PARTIALLY PROVED", {proved, not_p})

vcs = subp.new_input(reader=readers.ErrorListing("VC"),
                     union_name=subp.status_attr_id(),
                     inclusion=subp.slocs,
                     maps={"OK" : proved,
                           "KO" : not_p})
vcs2 = subp.new_input(reader=readers.ErrorListing("VCB"),
                      union_name=subp.status_attr_id(),
                      inclusion=subp.slocs,
                      maps={"OK" : proved,
                            "KO" : not_p})
vcs.load("obj/gnatprove.mrg")
vcs2.load("gnatprove2.out")
m.loads("program.json")

# Output results

for name in ["SUBPROGRAM.STATUS"]:
    for i in vcs.object.content():
        print i + " - " + name + " : " + str(vcs.object.follow(name, i))

for name in ["VCB.STATUS", "SUBPROGRAM.STATUS"]:
    for i in vcs2.object.content():
        print i + " - " + name + " : " + str(vcs2.object.follow(name, i))

for i in subp.object.content():
    name = "SUBPROGRAM.STATUS"
    print i + " - " + name + " : " + str(subp.object.follow(name, i))

print
print "**********"
print "* Test 4 *"
print "**********"
print

m = Merge()

subp = m.new_entity("SUBPROGRAM")
s    = subp.states

proved    = s.new_value("PROVED")
not_p     = s.new_value("NOT PROVED")
partial_p = s.name_and("PARTIALLY PROVED", {proved, not_p})

tested    = s.new_value("TEST PASSED")
not_t     = s.new_value("TEST FAILED")
partial_t = s.name_and("PARTIALLY TESTED", {tested, not_t})

ok = s.name_or("OK", {tested, proved})

tests = subp.new_input(reader=readers.ErrorListing("TEST", "PASSED"),
                       union_name=subp.status_attr_id(),
                       inclusion=subp.slocs,
                       maps={"OK" : tested,
                             "KO" : not_t})
vcs = subp.new_input(reader=readers.ErrorListing("VC"),
                     union_name=subp.status_attr_id(),
                     inclusion=subp.slocs,
                     maps={"OK" : proved,
                           "KO" : not_p})
tests.load("obj/gnattest.mrg")
vcs.load("obj/gnatprove.mrg")
m.loads("program.json")

# Output results

g = m.new_goal("OK", subp, ok)

for name in ["SUBPROGRAM.STATUS"]:
    for i in tests.object.content():
        print i + " - " + name + " : " + str(tests.object.follow(name, i))

for name in ["SUBPROGRAM.STATUS"]:
    for i in vcs.object.content():
        print i + " - " + name + " : " + str(vcs.object.follow(name, i))

for i in subp.object.content():
    name = "SUBPROGRAM.STATUS"
    print i + " - " + name + " : " + str(subp.object.follow(name, i))

g.print_errors(verbose=True)
