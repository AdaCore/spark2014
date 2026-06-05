from test_support import gnatprove

print("=== -v then -q ===")
gnatprove(opt=["-P", "test.gpr", "-v", "-q"], info=False)

print("=== -q then -v ===")
gnatprove(opt=["-P", "test.gpr", "-q", "-v"], info=False)
