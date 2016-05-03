from test_support import *
from time import sleep
import glob

conf_file = "test.whyconf"

proof = """admit.

Qed.
"""

def edit_proof():
    proof_file = glob.glob("proof/Coq/lemmas/*.v")[0]
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)

write_why3_config_file_with_coq(conf_file)
prove_all(opt=["-XRUN=1"], counterexample=False)
print "======================================="
prove_all(opt=["-XRUN=1", "--prover=coq", "--why3-conf=" + conf_file, "--limit-line=lemmas.ads:16"], steps=None, counterexample=False)
edit_proof()
prove_all(opt=["-XRUN=1"], counterexample=False)
print "======================================="
prove_all(opt=["-XRUN=2", "--prover=coq", "--why3-conf=" + conf_file, "--limit-line=lemmas.ads:18"], steps=None, counterexample=False)
prove_all(opt=["-XRUN=2"], counterexample=False)
print "======================================="
prove_all(opt=["-XRUN=1", "--prover=coq", "--why3-conf=" + conf_file, "--limit-line=lemmas.ads:16"], steps=None, counterexample=False)
prove_all(opt=["-XRUN=1"], counterexample=False)
