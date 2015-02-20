from test_support import *

gnatprove(opt=["-P", "test.gpr", "--warnings=error", "--report=all"])
