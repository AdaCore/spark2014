from test_support import *

gnat2why("pack.adb", opt=["-gnatd.G"])
gnat2why("pack.adb")
cat("pack.alfa")
