from test_support import *

gnatprove(opt=["-P", "test.gpr", "-q"], exit_status=1)
