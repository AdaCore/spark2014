from test_support import prove_all

# Do not display counterexamples, as they differ between platforms, due to
# spurious counterexamples being issued on Linux for non-linear VCs.
prove_all(counterexample=False, opt=["--proof-warnings"])
