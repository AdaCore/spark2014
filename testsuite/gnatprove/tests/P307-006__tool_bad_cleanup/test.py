from test_support import *

prove_all(opt=["-u", "foo.adb"])
with open("foo.spark_15_0_2", "r") as src:
    content = src.read()
with open(os.path.join("gnatprove", "foo.ali"), "w") as dst:
    dst.write(content)

prove_all()
