from test_support import prove_all

contains_manual_proof = True


def replay():
    prove_all(procs=10, counterexample=False, prover=["cvc5", "z3"], steps=10000)


if __name__ == "__main__":
    prove_all(replay=True, check_counterexamples=False)
