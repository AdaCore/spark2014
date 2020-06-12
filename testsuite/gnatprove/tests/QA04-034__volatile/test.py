from test_support import *

prove_all(prover=["cvc4"], steps=1, opt=["-u", "hw-dbc-transfer_rings.adb"])
