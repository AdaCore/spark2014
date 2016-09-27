from test_support import *
import shutil

prove_all(opt=["-u", "b.adb"])
sleep_on_windows(4)
shutil.copyfile("a.adb2", "a.adb")
prove_all(opt=["-u", "b.adb"])
