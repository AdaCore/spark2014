from test_support import *

prove(steps=400, opt=["--proof=then_split"])
# Cannot activate flow analysis. There is a legit issue with
# Ada.Text_IO [MA04-032]
