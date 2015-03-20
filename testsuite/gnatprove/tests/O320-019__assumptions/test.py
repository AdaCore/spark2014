from test_support import *

prove_all(opt=["--assumptions"])
cat (os.path.join("gnatprove", "gnatprove.out"), sort=True)
