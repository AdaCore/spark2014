from test_support import *

gnatprove (opt=["-P", "test.gpr", "--mode=all", "-f", "-q"])
