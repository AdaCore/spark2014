# disable z3 for cross-platform stability
from test_support import *

def replay():
    prove_all(steps=1600,procs=4)


prove_all(opt=["--replay"])
