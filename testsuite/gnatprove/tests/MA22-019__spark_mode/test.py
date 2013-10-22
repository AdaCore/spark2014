from test_support import *
from os.path import join

gnatprove(opt=["-P", "test.gpr", "--mode=flow"])
clean()

gnatprove(opt=["-P", "test.gpr", "--mode=prove"])
clean()

gnatprove(opt=["-P", "test.gpr", "--mode=all"])
clean()

gnatprove(opt=["-P", "test.gpr", "--mode=flow"])
gnatprove(opt=["-P", "test.gpr", "--mode=all"])
clean()
