from subprocess import call
from test_support import prove_all

prove_all(steps=8000)

call(["gnatmake", "-gnata", "-q", "test_vectors.adb"])
call(["./test_vectors"])
