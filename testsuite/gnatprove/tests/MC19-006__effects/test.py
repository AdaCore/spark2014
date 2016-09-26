from test_support import *
import shutil
import time

prove_all(opt=["-u", "b.adb"])
time.sleep(4)
shutil.copyfile("a.adb2", "a.adb")
prove_all(opt=["-u", "b.adb"])
