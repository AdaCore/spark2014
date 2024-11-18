from test_support import prove_all
import os

os.symlink("src2", "src")
prove_all()
