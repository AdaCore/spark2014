from test_support import prove_all

prove_all(opt=["-U"], project="Overview/overview")
prove_all(opt=["-U"], project="Flow_Analysis/flow_analysis")
prove_all(opt=["-U"], project="Proof_Integrity/proof_integrity")
prove_all(opt=["-U"], project="State_Abstraction/state_abstraction")
prove_all(
    steps=1000,
    sparklib=True,
    project="Functional_Correctness/functional_correctness",
    opt=[
        "-U",
        "--no-subprojects",
    ],
    check_counterexamples=False,
)
prove_all(opt=["-U"], project="Systems_Programming/systems_programming")
prove_all(opt=["-U"], project="Concurrency/concurrency")
prove_all(
    opt=["-U"],
    project="Object_Oriented_Programming/object_oriented_programming",
    check_counterexamples=False,
)
prove_all(
    sparklib=True,
    opt=["-U", "--no-subprojects"],
    project="Ghost_Code/ghost_code",
    check_counterexamples=False,
)
