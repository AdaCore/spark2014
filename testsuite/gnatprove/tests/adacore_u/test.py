from test_support import *
prove_all(opt=["-U", "-P", "Overview/overview"])
prove_all(opt=["-U", "-P", "Flow_Analysis/flow_analysis"])
prove_all(opt=["-U", "-P", "Proof_Integrity/proof_integrity"])
prove_all(opt=["-U", "-P", "State_Abstraction/state_abstraction"])
prove_all(steps=300, opt=["-U", "-P", "Functional_Correctness/functional_correctness"])
