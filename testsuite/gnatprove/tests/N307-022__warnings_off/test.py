from test_support import prove_all, gprbuild

# use project file compil.gpr for compilation...
gprbuild(["-q", "-P", "compil.gpr"])
# and project file test.gpr for verification
prove_all()
