from subprocess import call
from test_support import *

prove_all(steps=1000, opt=["-u", "bounded.adb", "unbounded.adb"])
# ADD AFTER NB19-026 AND NB20-048 ARE FIXED, AND REPLACE
#   @ ASSERT:FAIL
# BY
#   @ASSERT:FAIL
# IN THOSE TESTS AT THIS POINT
# "indefinite_bounded.adb", "indefinite_unbounded.adb"

# ADD ALSO THE TESTS BELOW AFTER THE ABOVE AND NB19-034 ARE FIXED, AND REPLACE
#   @ ASSERT:FAIL
# BY
#   @ASSERT:FAIL
# IN THOSE TESTS AT THIS POINT
# "indefinite_bounded_tagged.adb", "indefinite_unbounded_tagged.adb"

call(["gnatmake", "-gnata", "-q", "test_vectors.adb"])
call(["./test_vectors"])
