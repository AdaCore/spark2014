from test_support import prove_all

print("INLINING ENABLED:")
prove_all()
print

print("INLINING DISABLED:")
prove_all(opt=["--no-inlining"])
