from test_support import *

gcc ("cont.ads", opt=["-c"])
prove_all()
