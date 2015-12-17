from test_support import *
from os.path import join

do_flow()
result_file = os.path.join("gnatprove", "p.spark")
check_spec_spark(result_file, expected_len = 1)
