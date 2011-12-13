"""
This module contains support functions for all test.py
"""

import os
import sys
import glob
import re
from gnatpython.ex import Run

#  Change directory
TEST = sys.modules['__main__']
TESTDIR = os.path.dirname(TEST.__file__)
TEST_NAME = os.path.basename(TESTDIR)
os.chdir(TESTDIR)

altergo = "alt-ergo"
cpulimit = "why3-cpulimit"
timeout = "120"
regex = re.compile(r'\(([0-9]*)\)$')

def timing():
    """Invoke altergo on all VCs in the test directory

    PARAMETERS
    """
    file_list = sorted(glob.glob("*.why"))
    for f in file_list:
        cmd = [cpulimit, timeout, "0", "-h", altergo, f]
        process = Run(cmd)
        for line in process.out.splitlines():
            m = re.search(regex, line)
            if m:
                print f + " : " + m.group(1)
            else:
                print line
                print "error on file " + f
