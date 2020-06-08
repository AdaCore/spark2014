from test_support import *

print "###########"
print "compilation"
print "###########"
gcc("bad_assert.adb")

print ""
print "############"
print "verification"
print "############"
prove_all()
