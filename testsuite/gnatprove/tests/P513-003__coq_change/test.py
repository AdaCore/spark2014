from shutil import copyfile
from test_support import *
import glob

""" This test checks that a Coq proof becomes invalid when the source Ada file
changes to something invalid."""

proof = """
Open Scope Z_scope.

(* rewrite hypotheses *)
unfold dynamic_invariant1, in_range1 in h3.

(* apply arithmetic theorem *)
apply Z.quot_le_mono; auto with zarith.
intuition.
Qed.
"""

ads_file = "lemmas.ads"
new_file = "lemmas.ads.new"

def edit_proof():
    proof_file = glob.glob("proof/Coq/lemmas/*.v")[0]
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)

def edit_file():
    copyfile(new_file, ads_file)


print "======================================="
# This is used to create a .v file but fails because the coq proof is not done
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension")
# This edits the proof so that the Coq proof is now correct
edit_proof()
print "======================================="
# This makes things check that the proof is correct. After this the
# postcondition should be proved by Coq.
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
# Edit a file so that postcondition becomes false
edit_file()
sleep_on_windows(4)
# Coq proof should now fail
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension|Welcome|File")
print "======================================="
# Reports that the proof cannot be done
prove_all(counterexample=False)
