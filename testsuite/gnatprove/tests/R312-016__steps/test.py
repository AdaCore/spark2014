from test_support import *
import shutil


print("correct variant")
shutil.copyfile("ethernet_dissector.var2", "ethernet_dissector.adb")
# most VCs should be proved here
prove_all(steps=1, prover=["cvc4"])
shutil.copyfile("ethernet_dissector.var1", "ethernet_dissector.adb")
sleep(3)
print("incorrect variant")
# only a small number of VCs should become unproved
# the bug on this TN made a lot of these VCs unproved
prove_all(steps=1, prover=["cvc4"])
