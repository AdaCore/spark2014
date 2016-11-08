from test_support import *

gnatprove(opt=["-P", "test1.gpr"])
gnatprove(opt=["-P", "test1.gpr", "-aP=--codepeer=on"])
gnatprove(opt=["-P", "test2.gpr"])
gnatprove(opt=["-P", "test2.gpr", "-XBuild=Prod"])
