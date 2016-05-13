from shutil import copyfile
from test_support import *
from time import sleep
import glob

conf_file = "test.whyconf"

proof = """intros (val1_type,(val2_type,(denom_type,pre))).
Open Scope Z_scope.

(* rewrite hypotheses *)
unfold in_range1 in denom_type.

(* apply arithmetic theorem *)
apply Z.quot_le_mono; auto with zarith.

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


write_why3_config_file_with_coq(conf_file)
prove_all(prover=["cvc4"], counterexample=False)
print "======================================="
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=lemmas.ads:15"], steps=None, counterexample=False)
edit_proof()
print "======================================="
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=lemmas.ads:15"], steps=None, counterexample=False)
print "======================================="
edit_file()
sleep(4)
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=lemmas.ads:15"], steps=None, counterexample=False)
prove_all(counterexample=False)
