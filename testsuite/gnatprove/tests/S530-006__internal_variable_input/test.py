from test_support import do_flow

print("INLINING ENABLED:")
do_flow()
print()

print("INLINING DISABLED:")
do_flow(opt=["--no-inlining"])
