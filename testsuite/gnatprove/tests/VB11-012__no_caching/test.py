from test_support import gcc, prove_all

print("###########")
print("compilation")
print("###########")
gcc("noc.adb")
gcc("bad.ads")

print("")
print("############")
print("verification")
print("############")
prove_all(opt=["-u", "noc.adb"])
