from test_support import print_version, gnatprove

print_version()

for prover in ["cvc5", "z3", "altergo"]:
    gnatprove(opt=["-P", "test.gpr", "--clean"])
    print(f"====== {prover} ========")
    gnatprove(
        opt=[
            "-P",
            "test.gpr",
            "--report=fail",
            f"--prover={prover}",
            "-j",
            "0",
            "--quiet",
            "--output=oneline",
            "-A",
            "info-unrolling-inlining",
        ],
        info=False,
    )
