from test_support import gnatprove

gnatprove(opt=["-P", "toto.gpr", "file1.ads"])
gnatprove(opt=["-P", "toto2.gpr", "file1.ads"])
