from test_support import prove_all, TESTDIR
import os

contains_manual_proof = False
os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR


def replay():
    prove_all(procs=0, level=2)
    prove_all(procs=0, level=3)


if __name__ == "__main__":
    prove_all(replay=True)
