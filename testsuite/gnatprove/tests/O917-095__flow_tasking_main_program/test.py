from test_support import *

mains = [
	"main1.adb",
	"main2.adb",
	"main3.adb",
	"original_fake_main_func.ads",
	"renamed_fake_main_func.ads",
	"original_main_func.ads",
	"renamed_main_func.ads"
	]

for m in mains:
	prove_all(opt=["-P", "test.gpr", m])
