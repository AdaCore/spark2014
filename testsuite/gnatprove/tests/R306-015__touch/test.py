from test_support import *
import os

prove_all()
os.utime("bitwise_swap.adb", None)
prove_all()
