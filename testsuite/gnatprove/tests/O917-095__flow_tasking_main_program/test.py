from test_support import *

mains = [
	"main1.adb",
	"main2.adb",
	"main3.adb",
	"original_fake_main_func.ads",
	"renamed_fake_main_func.ads",
	"original_main_func.ads",
	"renamed_main_func.ads",
	"gen_inst.ads",
	"original_main_spec.ads",
	"original_main_body.adb",
	"main_with_no_spec.adb",
	"main_spec_only.ads",
	]

for m in mains:
	do_flow(opt=["-P", "test.gpr", m])
