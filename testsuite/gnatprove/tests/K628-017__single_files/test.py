from test_support import *

gnatprove(opt=["-P", "test.gpr", "s.adb", "--quiet", "-u"])
