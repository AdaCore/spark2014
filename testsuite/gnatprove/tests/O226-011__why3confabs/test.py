from test_support import *
import os, os.path

why3_path = os.path.join(os.getcwd(), "why3.conf")
prove_all(opt=["--why3-conf=" + why3_path])
