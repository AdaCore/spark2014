from test_support import prove_all
import os.path

prove_all(opt=["--subdirs", "toto"])

my_dir = os.path.join("toto", "gnatprove")
assert os.path.exists(my_dir)
assert os.path.isdir(my_dir)

prove_all(codepeer=True, opt=["--subdirs", "toto"], project="test2.gpr")

my_dir = os.path.join("obj", "toto", "gnatprove")
assert os.path.exists(my_dir)
assert os.path.isdir(my_dir)
