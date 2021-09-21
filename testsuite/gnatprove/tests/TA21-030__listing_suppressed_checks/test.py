from test_support import *

prove_all(opt=["--no-inlining"])
cat(os.path.join("gnatprove", "gnatprove.out"))
