from test_support import gnatprove

gnatprove(opt=["-P", "test.gpr", "-u", "client.adb"], sort_output=False)
