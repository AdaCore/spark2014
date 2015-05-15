from test_support import *
from time import sleep
import glob

conf_file = "test.whyconf"

proof = """admit.

Qed.
"""

def edit_proof():
    proof_file = glob.glob("proof/Coq/greatest_common_divisor/*.v")[0]
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)


write_why3_config_file_with_coq(conf_file)
prove_all()
print "======================================="
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=greatest_common_divisor.adb:10"])
print "======================================="
edit_proof()
# workaround for caching problem
touch("greatest_common_divisor.adb")
sleep(2)
prove_all(opt=["--prover=coq", "--why3-conf=" + conf_file, "--limit-line=greatest_common_divisor.adb:10"])
print "======================================="
prove_all()
