from test_support import prove_all
import os

curdir = os.getcwd()
try:
    os.chdir("src")
    os.symlink(os.path.join("..", "add.adb"), "add.adb")
finally:
    os.chdir(curdir)
prove_all()
