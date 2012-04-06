from test_support import *

out = gnatprove_(opt=["-P", "test.gpr", "--mode=detect"])
grep(".*error.*", out)

