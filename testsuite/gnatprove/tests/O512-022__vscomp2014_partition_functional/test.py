from test_support import *
"""  Counterexamples disabled on this test because CVC4 returns no
counterexample on Darwin and returns (dummy) counterexample on Linux.
See ticket OA21-004 for more information.
"""
# Do not use Z3, as the step limit fluctuates too much between platforms, thus
# making it impossible to share a common expected output when Z3 is used.
prove_all(prover=["cvc4", "altergo"],steps=1, counterexample=False)
