from test_support import *
from os.path import join

do_flow()
cat (os.path.join("gnatprove", "gnatprove.out"))
clean()

prove(opt=["--report=fail"])
cat (os.path.join("gnatprove", "gnatprove.out"))
clean()

prove_all(opt=["--report=fail"])
cat (os.path.join("gnatprove", "gnatprove.out"))
clean()

do_flow()
prove_all(opt=["--report=fail"])
cat (os.path.join("gnatprove", "gnatprove.out"))
clean()
