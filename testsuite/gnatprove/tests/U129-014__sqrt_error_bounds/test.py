from test_support import prove_all, TESTDIR
import os

os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR

if __name__ == "__main__":
    prove_all(check_counterexamples=False)
