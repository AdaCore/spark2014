from test_support import gnatprove, prove_all

prove_all()
gnatprove(opt=["-P", "test.gpr", "--clean"])
prove_all()
