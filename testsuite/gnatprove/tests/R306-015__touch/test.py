from test_support import prove_all
import os

prove_all()
os.utime("bitwise_swap.adb", None)
prove_all()
