from test_support import cat, prove_all
import os.path

prove_all()
cat(os.path.join("obj", "gnatprove", "gnatprove.out"))
