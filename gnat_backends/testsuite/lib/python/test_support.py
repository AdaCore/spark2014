
"""
This module contains support functions for all test.py
"""

import os
import sys
import re
import glob
import shutil
import json

max_steps = 500
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

def concat(file1, file2, out):
   """Concatenate two files

    PARAMETERS
      file1: name of the first file
      file2: name of the second file
      out: name of the target file
   """
   destination = open(out, 'wb')
   shutil.copyfileobj(open(file1, 'rb'), destination)
   shutil.copyfileobj(open(file2, 'rb'), destination)
   destination.close()

def read_dict_from_file(fn):
    """Fill a dictionary with keys from a file of the form
    key1 = val1
    key2 = val2

    PARAMETERS
        fn - input file name
    """
    keymap = {}
    for line in open(fn):
        ls = str.split(line, "=",1)
        if len(ls) > 1:
            key = str.strip(ls[0])
            val = str.strip(ls[1],"\"\n ")
            keymap[key] = val
        else:
            # only set po_name once
            if not keymap.has_key("po_name"):
                name = str.strip(line, "[] \n")
                keymap["po_name"] = name
    return keymap


def parse_altergo_result(output):
    """Transform the string, supposed to be an output of Alt-Ergo,
       into a list of booleans encoding success or failure of the VCs

    PARAMETERS
        output: the output of Alt-Ergo as string
    RETURNS
        a list of booleans
    """
    res = re.compile(".*:([^ ]*) *\(.*")
    incons = re.compile("Inconsistent assumption");
    status = []
    for line in str.splitlines(output):
        m = re.search(res, line)
        if m:
            s = m.group(1)
            status.append(s == "Valid")
        else:
            if re.search(incons, line):
                pass
            else:
                status.append(False)
    return status

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

def altergo(src, opt=None, verbose=True):
    """Invoke alt-ergo

    PARAMETERS
      src: source file to process
      opt: additional options to pass to alt-ergo
    Return: list of booleans
    """
    cmd = ["why-cpulimit","10","alt-ergo"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    # Remove Filename, linenumber and time of proof, just keep status
    res = re.compile(".*:([^ ]*) *\(.*")
    status = parse_altergo_result (process.out)
    if verbose:
        for b in status:
            if b:
                print "Valid"
            else:
                print "Failure"
    return status

def gnatprove(opt=["-P", "test.gpr"]):
    """Invoke gnatprove

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
    elif quick_mode():
        if os.path.exists("test.out"):
            cat("test.out", True)
    else:
        strlist = str.splitlines(process.out)
        strlist.sort()
        for line in strlist:
            print line

def prove(opt=[],steps=max_steps, mode="check"):
    """Call gnatprove with standard options"""
    opt += ["--report", "-P", "test.gpr"]
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

