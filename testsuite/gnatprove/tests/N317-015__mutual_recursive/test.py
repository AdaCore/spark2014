from test_support import *

# inlining of subp without decl under defug flag -gnatdQ
prove_all(opt=["-cargs", "-gnatdQ"])
