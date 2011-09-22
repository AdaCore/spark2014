
"""
This module contains support functions for all test.py
"""

import os
import sys
import re
import glob
import shutil
import json

max_steps = 700
parallel_procs = 1
#  Change directory

TEST = sys.modules['__main__']
TESTDIR = os.path.dirname(TEST.__file__)
TEST_NAME = os.path.basename(TESTDIR)
os.chdir(TESTDIR)

from gnatpython.ex import Run

def quick_mode():
    return "quick" in os.environ and os.environ["quick"] == "true"

def cat(filename, force_in_quick_mode=False):
    """Dump the content of a file on stdout

    PARAMETERS
      filename: name of the file to print on stdout
    """
    # do nothing in quick mode, as output is faked
    if not quick_mode() or force_in_quick_mode:
        if os.path.exists(filename):
            with open(filename, 'r') as f:
                print f.read()

def gcc(src, opt=None):
    """Invoke gcc

    PARAMETERS
      src: source file to process
      opt: additional options to pass to gcc
    """
    cmd = ["gcc", "-c"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    if process.status:
        print process.out

def gnat2why(src, opt=None):
    """Invoke gnat2why

    PARAMETERS
      src: source file to process
      opt: additional options to pass to gnat2why

    First call gcc on source file to produce ALI file.
    """
    gcc(src, opt=["-gnatd.F", "-gnat2012", "-gnatc"])
    cmd = ["gnat2why", "-gnatd.F", "-gnat2012"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    if process.status:
        print process.out
    elif quick_mode():
        if os.path.exists("test.out"):
            cat("test.out", True)

def why(src, opt=None):
    """Invoke why

    PARAMETERS
      src: source file to process
      opt: additional options to pass to why
    """
    cmd = ["why"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    if process.status:
        print process.out

def gnatprove_(opt=["-P", "test.gpr"]):
    """Invoke gnatprove, and in case of success return list of output lines

    PARAMETERS
    opt: options to give to gnatprove
    """
    cmd = ["gnatprove"]
    if quick_mode():
      cmd += ["--no-proof"]
    cmd += to_list(opt)
    process = Run(cmd)
    if process.status:
        print process.out
        return []
    elif quick_mode():
        if os.path.exists("test.out"):
            cat("test.out", True)
        return []
    else:
        strlist = str.splitlines(process.out)
        strlist.sort()
        return strlist

def gnatprove(opt=["-P", "test.gpr"]):
    """Invoke gnatprove

    PARAMETERS
    opt: options to give to gnatprove
    """
    out = gnatprove_(opt)
    for line in out:
        print line

def prove(opt=[],steps=max_steps, mode="check"):
    """Call gnatprove with standard options"""
    opt += ["--report=all", "-P", "test.gpr", "--quiet"]
    opt += ["--steps=%d"%(steps)]
    opt += ["--mode=%s"%(mode)]
    opt += ["-j%d"%(parallel_procs)]
    gnatprove(opt)

def prove_all(opt=[],steps=max_steps):
    """Call gnatprove with standard options to prove all VCs"""
    prove(opt,steps, "prove")

def to_list(arg):
    """Convert to list

    If arg is already a list, return it unchanged. Otherwise, if it is
    None, return an empty list. In any other case, wrap the argument in
    a list (that contains, as a consequence, only one element).
    """
    if arg is None:
        return []
    elif isinstance(arg, list):
        return arg
    else:
        return [arg]

def grep(regex, strlist, invert=False):
    """Filter a string list by a regex

    PARAMETERS
    regex: a string encoding a regular expression, using python regex syntax
    strlist: a list of strings
    """
    p = re.compile(regex)
    for line in strlist:
        m = re.match(p, line)
        if (invert and not m) or (not invert and m):
            print line

