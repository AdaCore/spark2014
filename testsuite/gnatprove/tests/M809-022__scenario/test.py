from test_support import *

prove_all(opt=["-Xmode=proof"])
clean()
prove_all()
