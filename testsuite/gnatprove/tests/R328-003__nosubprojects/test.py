from test_support import *
import os

os.mkdir("a_lib")

prove_all(project="c.gpr", opt=["--no-subprojects"])
