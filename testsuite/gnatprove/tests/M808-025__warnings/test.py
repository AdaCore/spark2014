from test_support import *

print "Stop at compilation:"
print "--------------------"
prove(opt=["-cargs", "-gnatwae"], mode="all")
clean()

print ""
print "Issue all compilation warnings, stop at flow warnings treated as errors:"
print "------------------------------------------------------------------------"
prove(opt=["--warnings=error", "-cargs", "-gnatwa"], mode="all")
clean()

print ""
print "Do not issue all compilation warnings, stop at flow warnings treated as errors:"
print "-------------------------------------------------------------------------------"
prove(opt=["--warnings=error"], mode="all")
clean()

print ""
print "Do not issue any compilation warnings, stop at flow warnings treated as errors:"
print "-------------------------------------------------------------------------------"
prove(opt=["--warnings=error", "-cargs", "-gnatws"], mode="all")
clean()

print ""
print "Issue all compilation warnings, issue flow warnings and continue:"
print "-----------------------------------------------------------------"
prove(opt=["--warnings=on", "-cargs", "-gnatwa"], mode="all")
clean()

print ""
print "Do not issue all compilation warnings, do not issue flow warnings and continue:"
print "------------------------------------------------------------------------"
prove(opt=["--warnings=on"], mode="all")
clean()

print ""
print "Do not issue any compilation warnings, issue flow warnings and continue:"
print "------------------------------------------------------------------------"
prove(opt=["--warnings=on", "-cargs", "-gnatws"], mode="all")
clean()


print ""
print "Issue all compilation warnings, do not issue flow warnings and continue:"
print "------------------------------------------------------------------------"
prove(opt=["--warnings=off", "-cargs", "-gnatwa"], mode="all")
clean()

print ""
print "Do not issue all compilation warnings, do not issue flow warnings and continue:"
print "-------------------------------------------------------------------------------"
prove(opt=["--warnings=off"], mode="all")
clean()

print ""
print "Do not issue any compilation warnings, do not issue flow warnings and continue:"
print "-------------------------------------------------------------------------------"
prove(opt=["--warnings=off", "-cargs", "-gnatws"], mode="all")
clean()
