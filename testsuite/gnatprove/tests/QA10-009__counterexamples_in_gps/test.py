from test_support import *

# This test is showing the difference of output between these two successive
# commands. Using prove_all (or removing -j0) does not show the same behavior.
gnatprove(opt=["-P", "test.gpr", "-j0", "-f"])
gnatprove(opt=["-P", "test.gpr", "-j0"])
