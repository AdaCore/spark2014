from test_support import prove_all, sleep
import shutil

prove_all()
sleep(10)
shutil.copyfile("a.adb2", "a.adb")
prove_all()
