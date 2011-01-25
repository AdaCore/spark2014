from test_support import *

gnat2why("empty.ads")
why("out.why",opt="--type-only")
