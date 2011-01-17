from test_support import *

gnat2why("assign.adb")
why("out.why",opt="--type-only")
cat("out.why")
