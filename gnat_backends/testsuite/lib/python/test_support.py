
"""
This module contains support functions for all test.py
"""

import os
import sys
import re
import glob
import shutil
import json

#  Change directory

TEST = sys.modules['__main__']
TESTDIR = os.path.dirname(TEST.__file__)
TEST_NAME = os.path.basename(TESTDIR)
os.chdir(TESTDIR)

from gnatpython.ex import Run

def cat(filename):
    """Dump the content of a file on stdout

    PARAMETERS
      filename: name of the file to print on stdout
    """
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
    gcc(src, opt=["-gnatd.F", "-gnat2012", "-gnata", "-gnato", "-gnatc"])
    cmd = ["gnat2why", "-gnatd.F", "-gnat2012", "-gnata", "-gnato",
           "-I" + get_path_to_adainclude()]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    if process.status:
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

def gnatprove(opt=["-P", "test.gpr", "-v"]):
    """Invoke gnatprove

    PARAMETERS
    opt: options to give to gnatprove
    """
    cmd = ["gnatprove"]
    cmd += to_list(opt)
    process = Run(cmd)
    if process.status:
        print process.out

def prove(src):
    """Prove all obligations from an Ada file

    PARAMETERS
      src: source file .adb or .adb to process

    Call gnat2why on source file, then why on the resulting file. Alt-Ergo is
    run on each generated VC independently.
    Collect results on a per-label basis and generate report
    """
    gnatprove()
    result = {}
    base, ext = os.path.splitext(src)
    for vc in open(os.path.join("gnatprove",base+".labels")):
        vc = str.strip(vc,"\n ")
        result[vc] = { 'valid' : [] , 'invalid': [] }
    for f in glob.glob(os.path.join("gnatprove", "*.xpl")):
        dic = read_dict_from_file(f)
        curname = dic['source_label']
        if not result.has_key(curname):
            print "missing label name:", curname
            return
        basename, ext = os.path.splitext(f)
        vc_result = os.path.join(basename + ".rgo")
        file_object = open(vc_result,"r")
        if parse_altergo_result(file_object.read())[0]:
            cur_result = 'valid'
        else:
            cur_result = 'invalid'
        result[curname][cur_result].append(dic["po_name"])
    for label,dic in result.iteritems():
        dic['valid'].sort()
        dic['invalid'].sort()
    print(json.dumps(result, sort_keys = True,indent=4))

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

def get_path_to_adainclude():
    """Return path to adainclude
    """
    cmd=[["gnatls", "-v"], ["grep", "adainclude"]]
    process = Run(cmd)
    return process.out.strip()

