import os.path
from test_support import cat, prove_all

prove_all()
cat(os.path.join("gnatprove", "gnatprove.out"))
