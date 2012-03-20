from test_support import *
import shutil
import time

prove_all()
time.sleep(3)
shutil.copyfile("a.adb2", "a.adb")
prove_all()

