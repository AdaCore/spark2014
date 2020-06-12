from test_support import *

contains_manual_proof = False

def replay():
    prove_all(level=2, opt=["--no-axiom-guard"], procs=0)
    
prove_all(opt=["--no-axiom-guard"],
          replay=True)
