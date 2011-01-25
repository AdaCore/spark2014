from test_support import *

gnat2why("signed.ads")
why("out.why",opt="--type-only")
