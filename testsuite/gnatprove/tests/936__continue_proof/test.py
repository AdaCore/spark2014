from test_support import prove_all

prove_all(
    steps=1500,
    opt=["--function-sandboxing=off"],
)
