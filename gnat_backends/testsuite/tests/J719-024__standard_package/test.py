from test_support import *

gnat2why("empty.ads", opt="-gnatS")
cat("standard.why")
