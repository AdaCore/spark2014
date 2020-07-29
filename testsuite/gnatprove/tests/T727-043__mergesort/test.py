from test_support import *

contains_manual_proof = False

def replay():
    prove_all(procs=0, level=2)

prove_all(replay=True)

#This test should have no fail, but currently we still have a failed termination
#check due to incomplete support of subprogram variants.
