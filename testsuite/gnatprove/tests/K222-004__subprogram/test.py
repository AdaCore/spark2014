from test_support import *

gnat2why("sub.adb", opt=["-gnat2012", "-gnatd.G"])
gnat2why("sub.adb", opt=["-gnat2012"])
