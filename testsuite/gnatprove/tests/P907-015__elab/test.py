from test_support import *

gnatprove(opt=["-P", "test.gpr", "--RTS=.", "--mode=check"])
