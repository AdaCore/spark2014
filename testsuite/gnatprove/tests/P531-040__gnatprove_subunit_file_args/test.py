from test_support import *

gnatprove (opt=["-P", "test.gpr", "-u", "parent-child-grandchild-proc.adb"])
