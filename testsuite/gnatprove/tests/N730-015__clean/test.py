from test_support import *
prove_all()
gnatprove(opt=["-P", "test.gpr", "--clean"])
prove_all()
