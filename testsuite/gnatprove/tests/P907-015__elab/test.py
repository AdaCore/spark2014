from test_support import gnatprove

gnatprove(opt=["-P", "test.gpr", "--RTS=.", "--mode=check"])
