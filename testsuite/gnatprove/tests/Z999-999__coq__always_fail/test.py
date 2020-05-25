from test_support import *
gcc("always_fail.adb", opt=["-c", "-gnatv"])
print("--")
gnatprove("--version")
