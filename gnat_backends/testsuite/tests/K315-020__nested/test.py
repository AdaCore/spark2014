from test_support import *
import glob

prove("nested.adb", ["-P", "test.gpr", "--all-vcs", "--report"])
