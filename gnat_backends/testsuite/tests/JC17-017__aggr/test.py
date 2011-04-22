from test_support import *

prove("p.adb",opt=["-P", "test.gpr", "--all-vcs"])
cat("gnatprove/p.alfa")
