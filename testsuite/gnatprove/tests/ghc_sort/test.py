from test_support import prove_all

contains_manual_proof = False


def replay():
    prove_all(prover=["z3", "cvc5", "altergo"], level=4, procs=10)


if __name__ == "__main__":
    prove_all(prover=["z3", "cvc5", "altergo"], replay=True)
