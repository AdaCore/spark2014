
"""
This module contains support functions for all test.py
"""

import os
import sys
import re
import glob
import shutil
import json

max_steps = 200
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

def quick_mode():
    return "quick" in os.environ and os.environ["quick"] == "true"

def debug_mode():
    return "debug" in os.environ and os.environ["debug"] == "true"

def verbose_mode():
    return "verbose" in os.environ and os.environ["verbose"] == "true"

def vc_timeout():
    if "vc_timeout" in os.environ:
        return int(os.environ["vc_timeout"])
    else:
        return default_vc_timeout

def xfail_test():
    if os.path.exists("test.opt"):
        p = re.compile("XFAIL")
        with open("test.opt", 'r') as f:
            for line in f:
                m = re.search(p, line)
                if m:
                    return True
    return False

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

def ls(directory=None):
    """ls wrapper for the testsuite

    PARAMETERS
       directory: the name of the directory to list the files of
    """
    if directory:
        cmd = ["ls", directory]
    else:
        cmd = ["ls"]
    process = Run(cmd)
    strlist = str.splitlines(process.out)
    strlist.sort()
    for line in strlist:
        print line

def gnat2why(src, opt=None):
    """Invoke gnat2why

    PARAMETERS
      src: source file to process
      opt: additional options to pass to gnat2why

    First call gcc on source file to produce ALI file.
    """
    cmd = ["gnat2why"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    if process.status:
        print process.out
    elif quick_mode():
        if os.path.exists("test.out"):
            cat("test.out", True)

def altergo(src, timeout=10, opt=None):
    """Invoke alt-ergo with why3-cpulimit wrapper

    PARAMETERS
      src: VC file to process
      timeout: timeout passed to why3-cpulimit
      opt: additional command line options for alt-ergo
    """
    cmd = ["why3-cpulimit", str(timeout), "0", "-h", "alt-ergo"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    print process.out

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
    global fake_output_generated
    cmd = ["gnatprove"]
    if quick_mode():
      cmd += ["--proof=no_wp"]
    if debug_mode():
      cmd += ["--debug"]
    if verbose_mode():
      cmd += ["--verbose"]
    cmd += to_list(opt)
    # Force the option -gnatd.V for SPARK 2014 extensions, to avoid having to
    # put it in all project files of tests.
    cmd += ["-cargs", "-gnatd.V"]
    process = Run(cmd)

    # In quick mode, ignore xfail tests by simply generating a dummy output
    if quick_mode() and xfail_test():
        if not fake_output_generated:
            fake_output_generated = True
            print "dummy output for XFAIL test"
        return []

    # If the command returned with an error, print the command output
    elif process.status:
        print process.out
        return []

    # Otherwise, in quick mode, ignore test output and copy instead the
    # expected output.
    elif quick_mode():
        if os.path.exists("test.out") and not fake_output_generated:
            fake_output_generated = True
            cat("test.out", True)
        return []

    # Otherwise, print the command output sorted
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

def prove(opt=None, steps=max_steps, vc_timeout=vc_timeout(), mode="prove"):
    """Call gnatprove with standard options"""
    if opt is None:
        opt = []
    opt += ["--report=all", "-P", "test.gpr", "--quiet"]
    opt += ["--timeout=%d"%(vc_timeout)]
    opt += ["--steps=%d"%(steps)]
    opt += ["--mode=%s"%(mode)]
    opt += ["-j%d"%(parallel_procs)]
    gnatprove(opt)

def do_flow(opt=None):
    """Call gnatprove with standard options for flow"""
    if opt is None:
        opt = []
    opt += ["-P", "test.gpr", "--quiet", "--mode=flow"]
    opt += ["-j%d"%(parallel_procs)]
    gnatprove(opt)

def prove_all(opt=None, steps=max_steps, vc_timeout=vc_timeout()):
    """Call gnatprove with standard options to prove all VCs"""
    prove(opt, steps, vc_timeout)

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

def check_dot_files(opt=None):
    """Call gnatprove with --mode=flow"""
    if opt is None:
        opt = []
    opt += ["-P", "test.gpr", "--quiet", "--mode=flow"]
    opt += ["-j%d"%(parallel_procs)]
    gnatprove(opt)

    """Create a list that contains all dot files lying under directory gnatprove"""
    dot_files = glob.glob('gnatprove/*.dot')

    """Dump the contents of all dot files on stdout"""
    for dot_file in sorted(dot_files):
        cat(dot_file)

