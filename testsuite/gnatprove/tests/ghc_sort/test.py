from test_support import prove_all

contains_manual_proof = False


def replay():
    prove_all(level=4, procs=0)


if __name__ == "__main__":
    prove_all(steps=0, replay=True)
