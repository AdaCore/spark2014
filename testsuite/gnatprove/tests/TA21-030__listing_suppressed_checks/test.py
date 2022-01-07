from test_support import cat, prove_all
import os.path

prove_all(opt=["--no-inlining"])
cat(os.path.join("gnatprove", "gnatprove.out"))
