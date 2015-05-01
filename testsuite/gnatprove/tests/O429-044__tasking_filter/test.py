from test_support import *
gnatprove(opt=["-P", "test.gpr", "--report=all", "--mode=check"])
