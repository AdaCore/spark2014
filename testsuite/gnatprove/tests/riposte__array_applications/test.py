from test_support import *

contains_manual_proof = False

def replay():
    prove_all(steps=2500,procs=0,opt=["--no-axiom-guard"])

prove_all(opt=["--no-axiom-guard"],replay=True)
