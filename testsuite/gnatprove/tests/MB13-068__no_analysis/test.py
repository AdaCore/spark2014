from test_support import *

gnatprove(opt=["-P", "test.gpr", "-u", "client.adb"])
