
"""
This module contains support functions for all test.py
"""

import os
import sys

#  Change directory

TEST = sys.modules['__main__']
TESTDIR = os.path.dirname(TEST.__file__)
TEST_NAME = os.path.basename(TESTDIR)
os.chdir(TESTDIR)

from gnatpython.ex import Run

def cat(filename):
    # ??? Missing doc
    f = open(filename, 'r')
    print f.read()

def gnat2why(src, opt=None):
    # ??? Missing doc
    cmd = ["gnat2why",
           "-I" + get_path_to_adainclude()]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    if process.status:
        print process.out

def to_list(arg):
    # ??? Missing doc
    if arg is None:
        return []
    elif isinstance(arg, type("")):
        return [arg]
    else:
        return arg

def get_path_to_adainclude():
    # ??? Missing doc
    cmd=[["gnatls", "-v"], ["grep", "adainclude"]]
    process = Run(cmd)
    return process.out.strip()

