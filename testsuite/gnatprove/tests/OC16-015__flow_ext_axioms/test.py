from test_support import check_all_spark, do_flow
import os.path

do_flow(opt=["--mode=flow"])
result_file = os.path.join("gnatprove", "p.spark")
check_all_spark(result_file, expected_len=1)
