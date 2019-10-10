from shutil import copyfile
from test_support import *
import glob

# This test follows the same pattern as P429-031__coq_change which is heavily
# commented.

# This test corresponds to the example of manual proof with Coq presented
# in section "7.9.3.4. Manual Proof Using Coq" of the SPARK User's Guide.
# Any change here should be reflected in the SPARK User's Guide.

proof = """
subst.
apply Z.quot_le_compat_l.
  apply Zle_trans with (m:=1%Z).
    (* 0 <= x *)
  - apply Zle_0_1.
    (* 1 <= x *)
  - unfold dynamic_invariant1, in_range1 in h1.
    apply h1. intuition.
  (* 0 < z <= y *)
  - unfold dynamic_invariant1, in_range1 in h3.
    intuition.
Qed.
"""

def edit_proof():
    proof_file = "proof/Coq/Nonlinear__pragargs__cmp.v"
    with open(proof_file, 'r') as file:
        content = file.read()
    content = str.replace(content, "Qed.", proof)
    with open(proof_file, 'w') as file:
        file.write(content)

print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=nonlinear.adb:4:11:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension")
edit_proof()
print "======================================="
prove_all(opt=["--prover=coq", "--limit-line=nonlinear.adb:4:11:VC_POSTCONDITION"], steps=None, counterexample=False, filter_output=".*Grammar extension")
print "======================================="
prove_all(prover=["altergo"], counterexample=False)
