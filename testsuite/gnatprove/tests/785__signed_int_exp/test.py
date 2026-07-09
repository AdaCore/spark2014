from test_support import clean, prove_all

# Proof coverage of exponentiation ("**") on signed integer types. Each
# prover is run in isolation, on a fresh proof session, so that its result
# is not influenced by results cached from another prover.

PROVERS_AND_STEPS = [
    ("cvc5", 1000),
    ("z3", 1000),
    ("altergo", 1000),
    ("colibri", 1000),
]

for prover, steps in PROVERS_AND_STEPS:
    clean()
    print(f"====== {prover} ========")
    prove_all(
        prover=[prover],
        steps=steps,
        report="provers",
        counterexample=False,
        check_counterexamples=False,
    )
