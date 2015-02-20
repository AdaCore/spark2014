from test_support import *

prove_all(opt=["-P", "test.gpr", "--warnings=error", "--report=all"])
