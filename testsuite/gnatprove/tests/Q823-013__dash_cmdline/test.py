from test_support import *

gnatprove(opt=["-P", "test.gpr", "-", "-", "-"])
# this test is about these dashes ^    ^    ^
