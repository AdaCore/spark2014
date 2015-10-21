from test_support import *
"""  Counterexamples disabled on this test because CVC4 returns no
counterexample on Darwin and returns (dummy) counterexample on Linux.
See ticket OA21-004 for more information.
"""
prove_all(steps=1600, counterexample=False)
