from test_support import *

gnatprove(opt=["-P", "test.gpr", "--mode=check", "-cargs", "-gnat2012"])
