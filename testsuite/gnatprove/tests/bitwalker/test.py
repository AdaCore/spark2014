from test_support import prove_all

contains_manual_proof = False


def replay():
    prove_all(opt=["--function-sandboxing=off"], level=4, procs=0)


if __name__ == "__main__":
    prove_all(opt=["--function-sandboxing=off"], replay=True)
