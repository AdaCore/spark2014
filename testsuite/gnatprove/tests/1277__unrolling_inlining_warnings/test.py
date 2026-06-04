from test_support import prove_all


print("---- default -------")
prove_all()

print("---- suppress negative warnings -------")
prove_all(opt=["-A", "unrolling-inlining-failures"])

print("---- negative warnings only -------")
prove_all(opt=["-A", "info-unrolling-inlining"])

print("---- suppress both categories -------")
prove_all(opt=["-A", "info-unrolling-inlining", "-A", "unrolling-inlining-failures"])
