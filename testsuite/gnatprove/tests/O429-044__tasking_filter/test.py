from test_support import *
from os.path import join

# The purpose of this test is to check that all the code is in SPARK

gnatprove(opt=["-P", "test.gpr", "--mode=check"])
result_file = os.path.join("gnatprove", "tasks.spark")
check_all_spark(result_file, expected_len = 11)
