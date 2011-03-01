from test_support import *

gnat2why("empty_proc.adb")
why("empty_proc.why",opt="--type-only")
