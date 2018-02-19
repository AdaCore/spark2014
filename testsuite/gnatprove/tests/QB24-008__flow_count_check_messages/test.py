from test_support import *

do_flow()

print "=" * 75
with open("gnatprove/gnatprove.out", "rU") as fd:
    tmp = fd.readlines()
print tmp[-1].strip()
