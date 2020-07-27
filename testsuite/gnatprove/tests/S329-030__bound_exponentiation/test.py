from test_support import *
import os

os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR
prove_all()
