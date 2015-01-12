from subprocess import call
from test_support import *
call(["gnatmake", "-gnatwa", "-P", "test.gpr"])
prove_all()
