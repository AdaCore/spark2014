from test_support import prove_all, TESTDIR
import os

os.environ["SPARKLIB_OBJECT_DIR"] = TESTDIR

prove_all(opt=["-U", "-P", "Overview/overview"])
prove_all(opt=["-U", "-P", "Flow_Analysis/flow_analysis"])
prove_all(opt=["-U", "-P", "Proof_Integrity/proof_integrity"])
prove_all(opt=["-U", "-P", "State_Abstraction/state_abstraction"])
prove_all(
    steps=700,
    opt=[
        "-U",
        "-P",
        "Functional_Correctness/functional_correctness",
        "--no-subprojects",
    ],
    check_counterexamples=False,
)
prove_all(opt=["-U", "-P", "Systems_Programming/systems_programming"])
prove_all(opt=["-U", "-P", "Concurrency/concurrency"])
prove_all(
    opt=["-U", "-P", "Object_Oriented_Programming/object_oriented_programming"],
    check_counterexamples=False,
)
prove_all(
    opt=["-U", "-P", "Ghost_Code/ghost_code", "--no-subprojects"],
    check_counterexamples=False,
)
