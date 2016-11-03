from test_support import *

# prove with CodePeer
print "------------"
print "CodePeer run"
print "------------"
prove_all(codepeer=True, prover=["altergo"])

# prove with provers
print ""
print "----------"
print "Prover run"
print "----------"
clean()
prove_all(prover=["z3"], steps=5000)
