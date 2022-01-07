from test_support import gnatprove, clean

gnatprove(opt=["-P", "test.gpr", "--mode=flow"])
clean()

gnatprove(opt=["-P", "test.gpr", "--mode=prove"])
clean()

gnatprove(opt=["-P", "test.gpr", "--mode=all"])
clean()

gnatprove(opt=["-P", "test.gpr", "--mode=flow"])
gnatprove(opt=["-P", "test.gpr", "--mode=all"])
clean()
