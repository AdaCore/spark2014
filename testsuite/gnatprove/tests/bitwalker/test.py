from test_support import prove_all

contains_manual_proof = False


def replay():
    prove_all(opt=["--function-sandboxing=off"], no_fail=True, level=3, procs=0)


if __name__ == "__main__":
    prove_all(opt=["--function-sandboxing=off"], no_fail=True, replay=True)
