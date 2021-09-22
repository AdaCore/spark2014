from e3.os.process import Run
from test_support import *
# disable colibri due to spurious output U716-002
prove_all(prover=["cvc4","altergo", "z3"])
p = Run(["gnatmake", "-P", "test.gpr", "-q"])
print(p.out)
p = Run(["./big_integers_test"])
print(p.out)
