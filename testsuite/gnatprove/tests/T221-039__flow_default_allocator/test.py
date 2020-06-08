from test_support import *
from gnatpython.env import putenv

putenv("SPARK_HEAP_OBJECT_DIR", TESTDIR)
do_flow()
