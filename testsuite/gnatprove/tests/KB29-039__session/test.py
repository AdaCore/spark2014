from test_support import *
import shutil
import time

prove_all()
shutil.copyfile("a.adb2", "a.adb")
time.sleep(3)
prove_all()

