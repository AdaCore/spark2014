from test_support import *

gnat2why("enum.ads")
why("out.why",opt="--type-only")
