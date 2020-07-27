from test_support import *

print("INLINING ENABLED:")
prove_all()
print

print("INLINING DISABLED:")
prove_all(opt=["--no-inlining"])
