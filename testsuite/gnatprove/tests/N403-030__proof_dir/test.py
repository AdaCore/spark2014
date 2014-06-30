from subprocess import call
from test_support import *

prove_all()
gnatprove(opt=["-P", "test.gpr", "--clean"])
ls("proof/dir/sessions")
ls()
