from test_support import *
import os

os.mkdir("a_lib")
os.mkdir("b_lib")

prove_all(project="main.gpr")
