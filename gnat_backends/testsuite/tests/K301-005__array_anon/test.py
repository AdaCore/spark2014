from test_support import *
import glob

prove("named.adb",opt=["-P", "test.gpr", "--all-vcs"])
