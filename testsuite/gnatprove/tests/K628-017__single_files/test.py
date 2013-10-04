from test_support import *

<<<<<<< HEAD
prove (opt=["s.adb", "-u"])
#Flow analysis not enabled [MA04-007]
=======
prove (opt=["s.adb", "-u"]) # flow disabled due to spurious errors (MA04-007)
>>>>>>> [MA04-007] Update tests to avoid flow errors
