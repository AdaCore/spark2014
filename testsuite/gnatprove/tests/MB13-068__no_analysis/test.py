from test_support import gnatprove, default_refiners_no_sort

gnatprove(
    opt=["-P", "test.gpr", "-u", "client.adb"], refiners=default_refiners_no_sort()
)
