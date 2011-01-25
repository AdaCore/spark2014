from test_support import *

gnat2why("empty_proc.adb")
why("out.why",opt="--type-only")
