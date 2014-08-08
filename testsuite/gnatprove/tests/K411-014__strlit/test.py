from test_support import *
import os.path
import glob

prove_all()
check_all_spark(os.path.join ("gnatprove", "strlit.spark"), expected_len = 2)
