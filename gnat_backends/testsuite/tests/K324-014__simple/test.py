from test_support import *

prove("qack.adb", ["--all-vcs", "--report", "-P" "test.gpr"])

