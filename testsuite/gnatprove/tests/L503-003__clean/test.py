from subprocess import call
from test_support import *

call(["mkdir", "-p", "obj"])
prove_all()
call(["gnatmake", "-P", "test_obj.gpr"])
prove_all(opt=["-P", "test_obj.gpr"])
gnatprove(opt=["-P", "test.gpr", "--clean"])
gnatprove(opt=["-P", "test_obj.gpr", "--clean"])
call(["ls", "obj"])
call(["ls"])
