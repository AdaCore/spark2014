from subprocess import call
from test_support import gnatprove, ls, prove_all, gprbuild

call(["mkdir", "-p", "obj"])
prove_all()
gprbuild(["-q", "-P", "test_obj.gpr"])
prove_all(opt=["-P", "test_obj.gpr"])
gnatprove(opt=["-P", "test.gpr", "--clean"])
gnatprove(opt=["-P", "test_obj.gpr", "--clean"])
ls("obj")
ls()
