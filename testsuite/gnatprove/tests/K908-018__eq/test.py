from test_support import *
from os.path import join
import json, time

# The purpose of this test is to check that all the code is in SPARK

prove_all()
time.sleep(1)
result_file = os.path.join("gnatprove", "pack.spark")
check_all_spark(result_file, expected_len = 3)
