from test_support import *

def replay():
    prove_all(procs=0, opt=["--why3-conf=why3.conf", "--level=2", "--no-axiom-guard"], prover=["cvc4","cvc4_alt","z3","altergo"], steps=None, vc_timeout=20)
    prove_all(procs=0, opt=["--why3-conf=why3.conf", "--level=3", "--no-axiom-guard"], prover=["cvc4","cvc4_alt","z3","altergo"], steps=None, vc_timeout=50)

prove_all(opt=["--why3-conf=why3.conf",
               "--replay",
               "--no-axiom-guard"],
          steps=None,
          vc_timeout=120,
          prover=["cvc4", "cvc4_alt", "z3", "altergo"])
