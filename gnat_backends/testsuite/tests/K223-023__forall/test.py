from test_support import *
import glob

prove("forall.adb",opt=["-P", "test.gpr", "--all-vcs"])
