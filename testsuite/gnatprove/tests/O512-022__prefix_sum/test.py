from test_support import *

contains_manual_proof = False

options = ["--no-axiom-guard",
           "--proof-warnings",
           "-u",
           "prefixsum.adb",
           "prefixsum_expanded.adb",
           "prefixsum_general.adb",
           "--no-counterexample"]

def replay():
    prove_all(procs=0, steps=0, vc_timeout=20, opt=options)

prove_all(replay=True, opt=options)
