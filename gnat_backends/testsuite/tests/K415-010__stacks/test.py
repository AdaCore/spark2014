from test_support import *
import glob

prove("stacks.adb",opt=["-P", "test.gpr", "--all-vcs"])
