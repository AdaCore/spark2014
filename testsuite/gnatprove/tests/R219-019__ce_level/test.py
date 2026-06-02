from test_support import gnatprove

gnatprove(opt=["-P", "test.gpr", "-q", "--report=all", "--level=2", "--output=oneline"])
