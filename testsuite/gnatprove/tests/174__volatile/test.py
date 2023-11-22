from test_support import gcc
from test_support import prove_all

gcc("test.adb")
prove_all()
