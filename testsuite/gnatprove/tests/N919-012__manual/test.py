from test_support import *

# this sets HOME to the current dir, so that why3 can pick up the why3.conf
os.environ["HOME"] = os.getcwd()

prove_all(opt=[ "--proof=progressive"])
prove_all(opt=["--prover=mycoq", "--proof=progressive"])
