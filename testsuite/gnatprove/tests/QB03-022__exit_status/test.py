from test_support import *

gnatprove(opt=["-P", "test.gpr", "-q", "--checks-as-errors"], exit_status=1)
