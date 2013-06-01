from test_support import *

gnat2why("p.adb", opt = ["-gnat2012", "-gnatd.G"])
gnat2why("p.adb", opt = ["-gnat2012"])
cat("p.alfa")
