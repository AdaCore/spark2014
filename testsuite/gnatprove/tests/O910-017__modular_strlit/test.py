from test_support import check_all_spark, prove_all
import os.path

prove_all()
check_all_spark(os.path.join("gnatprove", "strlit.spark"), expected_len=2)
