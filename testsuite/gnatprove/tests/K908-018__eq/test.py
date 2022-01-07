from test_support import check_all_spark, prove_all, sleep_on_windows
import os.path

# The purpose of this test is to check that all the code is in SPARK

prove_all()
sleep_on_windows(1)
result_file = os.path.join("gnatprove", "pack.spark")
check_all_spark(result_file, expected_len=3)
