from test_support import *

prove(steps=400,                  # flow requires fixed packages (M906-011)
      opt=["--proof=then_split"])
