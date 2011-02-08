from test_support import *

gnat2why("signed.ads")
why("signed.why",opt="--type-only")
