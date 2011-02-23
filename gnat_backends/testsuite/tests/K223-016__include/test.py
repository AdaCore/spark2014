from test_support import *
import glob

gnat2why("callee.adb")
gnat2why("caller.adb")
why("caller.why")
