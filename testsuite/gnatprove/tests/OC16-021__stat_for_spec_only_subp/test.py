from test_support import check_spec_spark, prove_all
import os.path

prove_all()
result_file = os.path.join("gnatprove", "p.spark")
check_spec_spark(result_file, expected_len=1)
