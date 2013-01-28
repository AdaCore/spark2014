from test_support import *

gnat2why("pack.adb", opt=["-gnat2012", "-gnatd.G"])
gnat2why("pack.adb", opt=["-gnat2012"])
