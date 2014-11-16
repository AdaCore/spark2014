from subprocess import call
from test_support import *

prove_all(steps=1000, opt=["-u", "bounded.adb", "unbounded.adb"])

# COMMENTED OUT UNTIL NB18-035 IS FIXED
#call(["gnatmake", "-gnata", "-q", "test_vectors.adb"])
#call(["./test_vectors"])
