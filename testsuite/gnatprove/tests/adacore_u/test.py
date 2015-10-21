from test_support import *
"""  Counterexamples disabled on this test because CVC4 returns no
counterexample on Darwin and returns (dummy) counterexample on Linux.
See ticket OA21-004 for more information.
"""
prove_all(opt=["-U", "-P", "Overview/overview"], counterexample=False)
prove_all(opt=["-U", "-P", "Flow_Analysis/flow_analysis"], counterexample=False)
prove_all(opt=["-U", "-P", "Proof_Integrity/proof_integrity"], counterexample=False)
prove_all(opt=["-U", "-P", "State_Abstraction/state_abstraction"], counterexample=False)
prove_all(opt=["-U", "-P", "Functional_Correctness/functional_correctness"], counterexample=False)
