from test_support import prove_all

# This should prove
prove_all(opt=["-cargs", "-gnateDSNEAK_EFFECT=False"])
# This should not prove
prove_all(opt=["-cargs", "-gnateDSNEAK_EFFECT=True"])
