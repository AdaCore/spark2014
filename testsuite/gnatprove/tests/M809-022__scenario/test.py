from test_support import clean, prove_all

prove_all(opt=["-Xmode=proof"])
clean()
prove_all()
