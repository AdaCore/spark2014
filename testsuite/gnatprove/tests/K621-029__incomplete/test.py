from test_support import *

out = gnatprove_(opt=["-P", "test.gpr", "--mode=detect"])
grep(".*(detailed|compilation error|failed).*", out,invert=True)

