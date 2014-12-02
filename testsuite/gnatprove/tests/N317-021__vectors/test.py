from subprocess import call
from test_support import *

# Remove analysis on selected files only after NC02-004 has been fixed
# AND REPLACE
#   @ ASSERT:FAIL
# BY
#   @ASSERT:FAIL
# IN THOSE TESTS AT THIS POINT
prove_all(steps=1000, opt = ["bounded.adb", "unbounded.adb",
                             "indefinite_bounded.adb", "indefinite_unbounded.adb"])

call(["gnatmake", "-gnata", "-q", "test_vectors.adb"])
call(["./test_vectors"])
