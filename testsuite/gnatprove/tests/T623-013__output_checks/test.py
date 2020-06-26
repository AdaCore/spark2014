from test_support import *

print("default command-line output")
print("---------------------------")
prove_all()
print("")

print("pretty output")
print("-------------")
prove_all(opt=["--output=pretty"])
print("")

print("one-line output")
print("---------------")
prove_all(opt=["--output=oneline"])
print("")

print("incorrect output value")
print("----------------------")
prove_all(opt=["--output=whatever"])
