from test_support import *
import os

os.environ["SPARK_HEAP_OBJECT_DIR"] = TESTDIR
do_flow()
