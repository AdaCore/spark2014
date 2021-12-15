from test_support import prove_all, sleep
import shutil

prove_all(opt=["-u", "b.adb"])
sleep(4)
shutil.copyfile("a.adb2", "a.adb")
prove_all(opt=["-u", "b.adb"])
