from test_support import *

gnat2why("empty.ads")
why("empty.why",opt="--type-only")
