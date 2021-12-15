from test_support import prove_all
from shutil import rmtree

prove_all(opt=["-XOBJ=A"])
rmtree("obj")
prove_all(opt=["-XOBJ=B"])
