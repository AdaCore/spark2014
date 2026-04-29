from test_support import RegexFilterRefiner, gnatprove

gnatprove(
    opt=["-P", "test.gpr", "--mode=prove", "--output=brief"],
    info=False,
    refiners=[RegexFilterRefiner(r"^Summary:", invert=False)],
)
