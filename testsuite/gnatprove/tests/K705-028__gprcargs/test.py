from test_support import *

gnatprove(opt=["-P", "test.gpr", "--mode=detect", "-cargs", "-gnat2012"])
