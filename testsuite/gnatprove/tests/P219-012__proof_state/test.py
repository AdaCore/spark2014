from test_support import *
import shutil

prove_all()

shutil.copy("main2.adx", "main.adb")
sleep_on_windows(4)
prove_all(opt=["--output-msg-only"])
