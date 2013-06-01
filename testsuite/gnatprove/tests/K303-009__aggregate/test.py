from test_support import *

# do not split unproved VCs to avoid reaching the timeout
prove_all(opt=["--proof=no_split"])
