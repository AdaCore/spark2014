import os

from test_support import clean, ls, prove_all

prove_all()
clean()
if os.path.isdir("lib"):
    ls("lib")
if os.path.isdir("lib_ali"):
    ls("lib_ali")
