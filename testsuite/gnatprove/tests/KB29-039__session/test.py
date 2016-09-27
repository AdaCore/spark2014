from test_support import *
import shutil

prove_all()
sleep_on_windows(10)
shutil.copyfile("a.adb2", "a.adb")
prove_all()
