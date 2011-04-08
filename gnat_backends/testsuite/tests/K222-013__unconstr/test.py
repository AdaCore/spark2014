from test_support import *
import glob

prove("unconstr.ads",opt=["-P", "test.gpr", "--all-vcs"])
