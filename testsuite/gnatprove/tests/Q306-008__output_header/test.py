from test_support import *

prove_all(cache_allowed=False)

# Only keep in output the lines that are common across calls on different
# dates and platforms
cat (os.path.join("gnatprove", "gnatprove.out"), start=4, end=5)
