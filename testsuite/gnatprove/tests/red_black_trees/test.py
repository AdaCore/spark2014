from test_support import *

def replay():
    prove_all(procs=0, opt=["--level=2", "--no-axiom-guard"], steps=None, vc_timeout=20)
    prove_all(procs=0, opt=["--level=3", "--no-axiom-guard"], steps=None, vc_timeout=50)

prove_all(opt=["--replay","--no-axiom-guard"])
