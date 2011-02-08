from test_support import *

gnat2why("prepost.adb", "-gnat2012")
why("prepost.why",opt="--type-only")
