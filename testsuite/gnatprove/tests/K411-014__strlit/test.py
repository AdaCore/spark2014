from test_support import *
import os.path
import glob

prove_all()
cat(os.path.join ("gnatprove", "strlit.spark"))
