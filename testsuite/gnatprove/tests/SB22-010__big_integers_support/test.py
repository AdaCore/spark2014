from gnatpython.ex import Run
from test_support import *
prove_all()
p = Run(["gnatmake", "-P", "test.gpr", "-q"])
print p.out
p = Run(["./big_integers_test"])
print p.out
