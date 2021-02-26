from test_support import *
import os

os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR

if __name__ == "__main__":
    prove_all()
