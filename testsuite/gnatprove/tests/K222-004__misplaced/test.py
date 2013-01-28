from test_support import *

gnat2why("misplaced.adb", opt=["-gnat2012", "-gnatd.G"])
gnat2why("misplaced.adb", opt=["-gnat2012"])
