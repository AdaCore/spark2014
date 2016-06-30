from test_support import *
import shutil
import time

prove_all()

shutil.copy("main2.adx", "main.adb")
time.sleep(4)
prove_all(opt=["--output-msg-only"])
