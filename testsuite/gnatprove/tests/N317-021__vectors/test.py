from subprocess import call
from test_support import *

prove_all()

call(["gnatmake", "-gnata", "-q", "test_vectors.adb"])
call(["./test_vectors"])
