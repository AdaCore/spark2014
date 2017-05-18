from test_support import *

prove_all(steps=10000,
          prover=["cvc4_alt", "z3"],
          no_fail=True,
          opt=["--no-axiom-guard",
               "--why3-conf=why3.conf",
               "-u",
               "simple_allocator.adb",
               "list_allocator.adb",
               "list_mod_allocator.adb"])
