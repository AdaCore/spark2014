from shutil import copyfile
from test_support import *
import glob

# This test is supposed to test whether a Coq proof can survive minor changes
# in the input file. See in-script comments for more details.

proof = """admit.

Admitted.
"""

ads_file = "lemmas.ads"
new_file = "lemmas.ads.new"

def edit_proof():
    proof_file = glob.glob("proof/Coq/lemmas__lemma_div_is_monotonic/*.v")[0]
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)

def edit_file():
    copyfile(new_file, ads_file)


# first call cvc4 to get rid of "easy" VCs. This call is removed.
print "======================================="
# first call to Coq, to produce a VC for the unproved postcondition
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension")
# "edit" the proof, in this case the proof is simply "admit"
edit_proof()
print "======================================="
# rerun gnatprove with Coq again, to check the proof; the coq proof should be
# proved now.
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
# now edit the source file, we want to know if gnatprove can still associate
# the VC with the proof. In fact here the file modification makes the VC
# unprovable in principle, but our "admit" proof above will still prove it. As
# this test is for tracking of VCs only, it's fine.
edit_file()
# on Windows, after editing a source file, need to wait because otherwise
# gprbuild will think nothing changed
sleep_on_windows(4)
# run gnatprove with Coq again to check proof
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15:14:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
# run gnatprove again with cvc4 to see full results
prove_all(counterexample=False)
