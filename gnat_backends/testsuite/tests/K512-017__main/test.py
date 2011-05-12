from test_support import *
import glob

prove("p.adb",opt=["-P", "test.gpr", "--all-vcs"])
