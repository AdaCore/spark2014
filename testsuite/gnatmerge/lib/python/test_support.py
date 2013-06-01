
"""
This module contains support functions for all test.py
"""

import os
import sys
import re
import glob
import shutil
import json

max_steps = 100
default_vc_timeout = 120
parallel_procs = 1
#  Change directory

# global flag for quick mode, so that the fake output is generated only once,
# even if original test calls gnatprove more than once
fake_output_generated = False

TEST = sys.modules['__main__']
TESTDIR = os.path.dirname(TEST.__file__)
TEST_NAME = os.path.basename(TESTDIR)
os.chdir(TESTDIR)

from gnatpython.ex import Run

def gnatmerge(script=None, project=None, options=None, sort_result=True):
    """Invoke gnatmerge

    PARAMETERS
      script:  merge script to process
      project: GNAT project file
      options: Additional options
    """
    cmd = ["gnatmerge",]
    if script is not None:
        cmd += ["-e", script]
    if project is not None:
        cmd += ["-P", project]
    if options is not None:
        cmd += options
    process = Run(cmd)
    if process.status:
        print "gnatmerge exit with status " + str(process.status)
    strlist = str.splitlines(process.out)
    if sort_result:
        strlist.sort()
    for line in strlist:
        print line
