import glob
from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, steps=0, vc_timeout=20, opt=["--no-axiom-guard"])

prove_all(replay=True, opt=["--no-axiom-guard"])
