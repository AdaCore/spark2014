from test_support import *

gnatprove(opt=["-q", "-k", "-P", "check_fast.gpr", "--mode=check"])
gnatprove(opt=["-q", "-k", "-P", "check_all.gpr", "--mode=flow"])
gnatprove(opt=["-q", "-k", "-P", "test.gpr", "--mode=flow"])
