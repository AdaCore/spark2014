from test_support import prove_all

contains_manual_proof = False


def replay():
    prove_all(procs=0, counterexample=False, level=4, check_counterexamples=False)


if __name__ == "__main__":
    prove_all(replay=True, check_counterexamples=False)
