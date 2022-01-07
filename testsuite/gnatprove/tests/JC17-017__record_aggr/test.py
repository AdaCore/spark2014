from test_support import check_all_spark, prove_all
import os.path

prove_all()
check_all_spark(os.path.join("gnatprove", "p.spark"), expected_len=11)
