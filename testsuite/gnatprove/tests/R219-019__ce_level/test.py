from test_support import *

gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=4", "--output=oneline"])
