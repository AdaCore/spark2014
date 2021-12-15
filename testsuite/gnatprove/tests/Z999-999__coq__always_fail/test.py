from test_support import gcc, gnatprove

gcc("always_fail.adb", opt=["-c", "-gnatv"])
print("--")
gnatprove("--version")
