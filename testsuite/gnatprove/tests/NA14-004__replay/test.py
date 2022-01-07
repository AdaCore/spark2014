from test_support import prove_all

contains_manual_proof = False

prove_all()
# replaying GNATprove should issue exactly the same messages
prove_all()
# replaying GNATprove should issue exactly the same messages
prove_all()
