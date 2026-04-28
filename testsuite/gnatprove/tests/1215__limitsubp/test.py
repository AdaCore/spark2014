from test_support import gnatprove, prove_all

prove_all()
gnatprove(opt=["-P", "test.gpr", "--clean"])
# nonexistent subp in p
gnatprove(opt=["-P", "test.gpr", "--limit-subp=p.ads:4"], exit_status=1)
print("====== same error in quiet mode ================")
gnatprove(opt=["-P", "test.gpr", "--limit-subp=p.ads:4", "-q"], exit_status=1)
