from subprocess import call
from test_support import *

prove_all(steps=1000, opt=["-u", "bounded.adb", "unbounded.adb"])
# ADD AFTER NB18-014, NB19-023 AND NB19-026 ARE FIXED, AND REPLACE
#   @ ASSERT:FAIL
# BY
#   @ASSERT:FAIL
# IN THOSE TESTS AT THIS POINT
# "indefinite_bounded.adb", "indefinite_unbounded.adb"

# COMMENTED OUT UNTIL NB18-035 IS FIXED
#call(["gnatmake", "-gnata", "-q", "test_vectors.adb"])
#call(["./test_vectors"])
