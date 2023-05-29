import os
import stat
from test_support import prove_all

os.mkdir("obj")
os.chmod("obj", stat.S_IEXEC | stat.S_IREAD)
prove_all()
os.mkdir("obj_a")
os.mkdir("a_lib")
os.chmod("obj_a", stat.S_IEXEC | stat.S_IREAD)
prove_all(project="main.gpr")
