from test_support import *
from gnatpython.env import putenv

putenv("SPARK_LEMMAS_OBJECT_DIR", TESTDIR)
prove_all()
