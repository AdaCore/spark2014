from test_support import *

gnat2why("enum.ads")
why("enum.why",opt="--type-only")
