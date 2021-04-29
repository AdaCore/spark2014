from subprocess import call

# Directly use CALL from python, because our GNATPROVE routine adds "-k"
# switch, which prevents this test from crashing.
#
# A dummy test.gpr config is provided explicitly by this test, as it will not
# be created by the GNATPROVE routine.

call(["gnatprove", "-P", "test.gpr", "--mode=check_all", "p.ads", "--output=brief"])
