from e3.os.process import Run
from test_support import prove_all, gprbuild, log_sorted

contains_manual_proof = False


def replay():
    prove_all(level=4, procs=0, sparklib=True, sparklib_bodymode=True)


if __name__ == "__main__":
    prove_all(replay="session", sparklib=True, sparklib_bodymode=True)

    gprbuild(["-q", "-P", "test.gpr"], sparklib_bodymode=True)
    process = Run(["./obj/test"])
    log_sorted(None, str.splitlines(process.out))
