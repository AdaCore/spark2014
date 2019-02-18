from test_support import *
from gnatpython.env import putenv


putenv("SPARK_LEMMAS_OBJECT_DIR", TESTDIR)
prove_all(no_fail=True, level=2, opt=["-u", "test_higher_order.ads"])
