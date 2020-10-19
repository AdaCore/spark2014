from test_support import *

gnatprove(opt=["-P", "test.gpr", "-q", "--checks-as-errors", "--output=oneline"], exit_status=1)
