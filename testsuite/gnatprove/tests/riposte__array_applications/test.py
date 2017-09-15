from test_support import *

def replay():
    prove_all(steps=1600,procs=0,opt=["--no-axiom-guard"])

prove_all(opt=["--replay", "--no-axiom-guard"])
