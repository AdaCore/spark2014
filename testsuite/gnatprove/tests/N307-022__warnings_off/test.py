from subprocess import call
from test_support import prove_all

# use project file compil.gpr for compilation...
call(["gprbuild", "-q", "-P", "compil.gpr"])
# and project file test.gpr for verification
prove_all()
