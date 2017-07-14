from test_support import *
# allow parallelism on this test which has a handful of very long-running VCs (~2 minutes each)
prove_all(steps=500000,
          prover=["cvc4_cbqi", "cvc4"],
          opt=["--why3-conf=why3.conf"],
          counterexample=False,
          procs=8,
          # no_fail=True,
          subdue_flow=True)
