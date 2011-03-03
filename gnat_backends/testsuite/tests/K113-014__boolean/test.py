from test_support import *

gnat2why("bool.ads")
why("bool.why", ["--type-only"])
