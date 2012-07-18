
import readers
from merges import *

print
print "**********************************************************"
print "* Merge gnattests/gnatprove results and produce a report *"
print "**********************************************************"
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
                       maps={"OK" : tested,
                             "KO" : not_t})
vcs = subp.new_input(reader=readers.ErrorListing("VC"),
                     maps={"OK" : proved,
                           "KO" : not_p})
tests.load("gnattest.out")
vcs.load("gnatprove.out")
m.loads("program.json")

# Output results

g = m.new_goal("OK", subp, ok)

g.print_errors()
