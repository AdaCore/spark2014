from test_support import gnatprove

gnatprove(
    opt=["-P", "test.gpr", "-q", "--checks-as-errors=on", "--output=oneline"],
    exit_status=1,
)
