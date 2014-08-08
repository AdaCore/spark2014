from test_support import *
from os.path import join

prove_all()
check_all_spark (os.path.join("gnatprove", "pack.spark"),
                 expected_len = 10)
