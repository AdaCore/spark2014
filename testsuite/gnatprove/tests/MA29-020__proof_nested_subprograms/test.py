from test_support import *

prove_all(steps=800)
cat (os.path.join("gnatprove", "gnatprove.out"))
