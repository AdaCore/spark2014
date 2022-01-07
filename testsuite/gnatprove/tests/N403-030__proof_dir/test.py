from test_support import gnatprove, ls, prove_all

prove_all(cache_allowed=False)
gnatprove(opt=["-P", "test.gpr", "--clean"])
ls("proof/dir/sessions")
ls()
