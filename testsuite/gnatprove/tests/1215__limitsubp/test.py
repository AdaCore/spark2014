from test_support import gnatprove, prove_all

prove_all()
# nonexistent subp in p
gnatprove(opt=["-P", "test.gpr", "--limit-subp=p.ads:4"])
