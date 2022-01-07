from test_support import prove_all
import os

os.mkdir("a_lib")
os.mkdir("b_lib")

prove_all(project="main.gpr")
