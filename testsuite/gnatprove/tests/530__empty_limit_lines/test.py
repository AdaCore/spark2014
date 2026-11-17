from test_support import gnatprove

print("=== empty limit-lines file ===")
gnatprove(
    opt=["-P", "test.gpr", "-u", "main.adb", "--limit-lines=empty.txt"], exit_status=0
)

print("=== no limit switch ===")
gnatprove(opt=["-P", "test.gpr", "-u", "main.adb"], exit_status=0)
