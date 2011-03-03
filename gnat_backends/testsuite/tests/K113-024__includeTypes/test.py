from test_support import *

gnat2why("basictypes.ads")
gnat2why("iandatypes.ads")
why("iandatypes.why","--type-only")
why("basictypes.why","--type-only")
