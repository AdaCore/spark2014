from shutil import copyfile
from test_support import *
import glob

proof = """admit.

Admitted.
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


prove_all(prover=["cvc4"], counterexample=False)
print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15"], steps=None, counterexample=False, filter_output=".*Grammar extension")
edit_proof()
print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
edit_file()
sleep_on_windows(4)
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15"], steps=None, counterexample=False, filter_output=".*Grammar extension")
prove_all(counterexample=False)
