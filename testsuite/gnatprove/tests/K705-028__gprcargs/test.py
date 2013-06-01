from test_support import *

gnatprove(opt=["-P", "test.gpr", "--mode=check", "-q", "-cargs", "-gnat2012"])
