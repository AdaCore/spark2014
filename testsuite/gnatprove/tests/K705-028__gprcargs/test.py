from test_support import gnatprove

gnatprove(opt=["-P", "test.gpr", "--mode=check", "-cargs", "-gnat2012"])
