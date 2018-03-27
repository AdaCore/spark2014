from test_support import *
import os

os.mkdir("a_lib")

prove_all(project="a.gpr")
prove_all(project="c.gpr")
