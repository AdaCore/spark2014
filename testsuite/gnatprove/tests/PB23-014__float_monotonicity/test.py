from test_support import prove_all, TESTDIR
import os

os.environ["SPARK_LEMMAS_OBJECT_DIR"] = TESTDIR
prove_all(opt=["-u", "add.adb", "mul.adb"])
