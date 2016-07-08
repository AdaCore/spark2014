from test_support import *
import os.path

prove_all()
cat(os.path.join("obj", "gnatprove", "gnatprove.out"))
