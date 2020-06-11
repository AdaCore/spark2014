from test_support import *

prove_all(ada=2012, prover=["cvc4"], steps=1, opt=["-u", "hw-dbc-transfer_rings.adb"])
