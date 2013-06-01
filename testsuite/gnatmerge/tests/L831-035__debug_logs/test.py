from test_support import *
import os

os.environ["PYTHONPATH"] = "%s:%s" % (os.getcwd(), os.environ["PYTHONPATH"])
gnatmerge(script='test_debug_traces.py',
          options=["--debug_conf=debug.conf",],
          sort_result=False)
