from test_support import *

prove_all(no_fail=True, prover=["alt-ergo"], opt=["--proof-warnings"], steps=5000)
