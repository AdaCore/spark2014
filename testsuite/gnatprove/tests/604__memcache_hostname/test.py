from test_support import prove_all

prove_all(
    opt=["--memcached-server=unknown:11211"],
    filter_output="gnatprove: \\[(\\d+)\\] ((Host not found)|(Try again))",
)
