from test_support import prove_all
import os

os.mkdir("a_lib")

prove_all(project="a_build.gpr")
print("------------------")
prove_all(project="c.gpr")
