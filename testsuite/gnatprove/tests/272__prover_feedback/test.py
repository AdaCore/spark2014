from test_support import default_refiners_no_sort, gnatprove, prove_all


common = {
    "prover": ["altergo"],
    "steps": 1,
    "counterexample": False,
    "check_counterexamples": False,
    "refiners": default_refiners_no_sort(),
}

print("oneline disabled")
prove_all(**common)

print("oneline enabled")
prove_all(**common, prover_feedback=True)

print("pretty enabled")
gnatprove(
    opt=[
        "-P",
        "test.gpr",
        "--output=pretty",
        "--warnings=continue",
        "--assumptions",
        "--steps=1",
        "--timeout=30",
        "--memlimit=2000",
        "--mode=all",
        "--prover=altergo",
        "--counterexamples=off",
        "--check-counterexamples=off",
        "--debug-no-cache-output",
    ],
    report="provers",
    refiners=default_refiners_no_sort(),
    prover_feedback=True,
)
