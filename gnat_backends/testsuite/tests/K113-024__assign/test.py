from test_support import *

gnat2why("assign.adb")
why("assign.why",opt="--type-only")
