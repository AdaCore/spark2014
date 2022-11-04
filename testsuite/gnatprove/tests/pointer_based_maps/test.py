from test_support import prove_all

contains_manual_proof = False


def replay():
    prove_all(level=2, opt=["--function-sandboxing=off"], procs=0)


if __name__ == "__main__":
    prove_all(opt=["--function-sandboxing=off"], replay=True)
