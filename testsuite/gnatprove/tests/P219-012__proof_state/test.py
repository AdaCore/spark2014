from test_support import sleep_on_windows, prove_all
import shutil

prove_all()

shutil.copy("main2.adx", "main.adb")
sleep_on_windows(4)
prove_all(opt=["--output-msg-only"])
