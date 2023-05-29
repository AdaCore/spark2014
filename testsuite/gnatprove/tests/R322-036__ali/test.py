import os
import shutil
import stat
from test_support import prove_all

prove_all(project="a_build.gpr")
print("------------------")
prove_all(project="b_build.gpr")
print("------------------")
shutil.rmtree(os.path.join("a_lib", "gnatprove"))
os.chmod("a_lib", stat.S_IREAD | stat.S_IEXEC)
os.mkdir("a_obj")
os.chmod("a_obj", stat.S_IREAD | stat.S_IEXEC)
prove_all(project="main.gpr")
