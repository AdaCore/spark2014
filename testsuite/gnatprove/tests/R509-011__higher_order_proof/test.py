from test_support import *
from gnatpython.env import putenv

contains_manual_proof = False

def replay():
    prove_all(procs=10, steps=0, level=2, opt=["-u", "test_higher_order.ads"])

putenv("SPARK_LEMMAS_OBJECT_DIR", TESTDIR)
prove_all(steps=0, replay=True, opt=["-u", "test_higher_order.ads"])
