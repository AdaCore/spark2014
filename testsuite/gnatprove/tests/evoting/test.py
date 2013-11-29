from test_support import *

prove(steps=900, opt=["--proof=progressive"])

# Cannot activate flow analysis. There is a legit issue with
# Ada.Text_IO [MA04-032]
