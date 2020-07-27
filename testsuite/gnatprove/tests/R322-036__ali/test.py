from test_support import *

prove_all(project="a_build.gpr")
print("------------------")
prove_all(project="b_build.gpr")
print("------------------")
prove_all(project="main.gpr")
