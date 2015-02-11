from test_support import *

gnatprove(opt=["-P", "scbe.gpr", "--warnings=error", "--report=all"])
