from test_support import prove_all

contains_manual_proof = False


def replay():
    prove_all(opt=["--no-axiom-guard"], level=1, procs=10, steps=0)
    prove_all(opt=["--no-axiom-guard"], level=3, procs=10, steps=0)


if __name__ == "__main__":
    prove_all(opt=["--no-axiom-guard"], replay=True)
