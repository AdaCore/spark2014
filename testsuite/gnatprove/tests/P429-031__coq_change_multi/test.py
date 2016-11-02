from shutil import copyfile
from test_support import *
import glob

proof = """admit.

Admitted.
"""

def edit_proof(num):
    proof_file = glob.glob("proof/Coq/lemmas/*monotonic" + str(num) + "*.v")[0]
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)

prove_all(prover=["cvc4"], counterexample=False)
print "======================================="
prove_all(opt=["--limit-line=lemmas.ads:15"], steps=None, counterexample=False)
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15"], steps=None, counterexample=False, filter_output=".*Grammar extension")
edit_proof(1)
print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:15"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
prove_all(opt=["--limit-subp=lemmas.ads:17", "--limit-line=lemmas.ads:24"], steps=None, counterexample=False)
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:24"], steps=None, counterexample=False, filter_output=".*Grammar extension")
edit_proof(2)
print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=lemmas.ads:24"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
prove_all(counterexample=False)
