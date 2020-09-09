from test_support import *

# Do not use Z3 which causes diffs between platforms. And Alt-Ergo doesn't
# do anything here.
prove_all(opt=["--no-axiom-guard",
               "--prover=cvc4",
               "--proof-warnings"],
          steps=3000,
          counterexample=False)
