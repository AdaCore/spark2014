from test_support import *

print ("Replay removes the obsolete proofattempts in manual proof:")
prove_all(opt=["--replay"])
print ("Now launching gnatprove in normal mode; it should reuse the proof:")
prove_all(prover=["cvc4"], level=0)
