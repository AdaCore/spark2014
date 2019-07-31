from test_support import *
import glob

proof = """admit.

Admitted.
"""

def edit_proof():
    proof_file = glob.glob("proof/Coq/greatest_common_divisor__g_c_d/*.v")[0]
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)


prove_all(counterexample=False)
print "======================================="
prove_all(opt=["--prover=Coq", "--limit-line=greatest_common_divisor.adb:10"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
edit_proof()
# workaround for caching problem
touch("greatest_common_divisor.adb")
sleep_on_windows(2)
prove_all(opt=["--prover=Coq", "--limit-line=greatest_common_divisor.adb:10"], steps=None, counterexample=False, filter_output=".*Grammar extension" )
print "======================================="
prove_all(counterexample=False)
