from test_support import *
from shutil import rmtree

prove_all(opt=["-XOBJ=A"])
rmtree("obj")
prove_all(opt=["-XOBJ=B"])
