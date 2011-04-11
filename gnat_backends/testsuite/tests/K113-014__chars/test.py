from test_support import *
import glob

prove("chars.adb",opt=["-P", "test.gpr", "--all-vcs"])
