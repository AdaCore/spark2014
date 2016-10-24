from test_support import *

# prove with CodePeer
print "------------"
print "CodePeer run"
print "------------"
prove_all(codepeer=True, prover=["altergo"], steps=1)

# prove with provers
print ""
print "----------"
print "Prover run"
print "----------"
prove_all(prover=["z3"])
