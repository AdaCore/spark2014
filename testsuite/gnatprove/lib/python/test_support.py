
"""
This module contains support functions for all test.py
"""

import os
import sys
import re
import glob
import json
from test_util import sort_key_for_errors

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


def print_sorted(strlist):
    strlist.sort(key=sort_key_for_errors)
    for line in strlist:
        print line


def cat(filename, force_in_quick_mode=False, sort=False):
    """Dump the content of a file on stdout

    PARAMETERS
      filename: name of the file to print on stdout
    """
    # do nothing in quick mode, as output is faked
    if not quick_mode() or force_in_quick_mode:
        if os.path.exists(filename):
            with open(filename, 'r') as f:
                if sort:
                    print_sorted(f.readlines())
                else:
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
    print_sorted(str.splitlines(process.out))


def matches(comp_reg, s, invert):
    """decide whether string s matches the compiled regex comp_reg

    PARAMETERS
    comp_reg: a compiled regex
    s: a string to be matched
    invert: if false, negate the result
    """
    m = re.match(comp_reg, s)
    return (invert and not m) or (not invert and m)


def check_marks(strlist):
    """Checks that marks in source code have a matching result.

    Given the output from flow analysis and/or proof, check that all marks
    mentioned in source files have a matching expected result, where source
    files are taken to be the *.ad? files in the current directory.

    Marks are any strings in the source that have the format
        @TAG:RESULT
    where both TAG and RESULT are alphanumeric strings without space, possibly
    with underscores. A tag denotes a line some result is expected (typically
    this marker will be put in comments).

    TAG is either:
    - a check (RANGE_CHECK, DIVISION_CHECK, etc), or
    - a flow message (UNINIT, DEPENDS, etc).

    The complete list of tags is given by functions is_flow_tag and
    is_proof_tag.

    RESULT is either
    - PASS/FAIL for checks, or
    - ERROR/CHECK/WARN for flow messages.

    Case does not matter for the tag or result, although UPPERCASE is better in
    source code to easily locate the marks visually.

    """
    files = glob.glob("*.ad?")
    is_msg = re.compile(r"(\w*\.ad.?):(\d*):\d*:" +
                        r" (info|warning|low|medium|high)?(: )?(.*$)")
    is_mark = re.compile(r"@(\w*):(\w*)")

    def get_tag(text):
        """Returns the tag for a given message text, or None if no tag is
        recognized."""

        # flow analysis tags

        # When adding a tag in this section, you need also to update the
        # function is_flow_tag below.
        if 'dependency' in text:
            return 'DEPENDS'
        elif 'global' in text:
            return 'GLOBAL'
        elif 'initialized' in text:
            return 'INITIALIZED'

        # proof tags

        # When adding a tag in this section, you need also to update the
        # function is_proof_tag below.
        if 'division check' in text or 'divide by zero' in text:
            return 'DIVISION_CHECK'
        elif 'index check' in text:
            return 'INDEX_CHECK'
        elif 'overflow check' in text:
            return 'OVERFLOW_CHECK'
        elif 'range check' in text:
            return 'RANGE_CHECK'
        elif 'length check' in text:
            return 'LENGTH_CHECK'
        elif 'discriminant check' in text:
            return 'DISCRIMINANT_CHECK'
        elif 'default initial condition' in text:
            return 'DEFAULT_INITIAL_CONDITION'
        elif 'initial condition' in text:
            return 'INITIAL_CONDITION'
        elif 'precondition' in text or 'nonreturning' in text:
            if 'of main program' in text:
                return 'PRECONDITION_MAIN'
            else:
                return 'PRECONDITION'
        elif 'postcondition' in text:
            return 'POSTCONDITION'
        elif 'refined post' in text:
            return 'REFINED_POST'
        elif 'contract case' in text:
            if 'disjoint' in text and 'contract cases' in text:
                return 'DISJOINT_CONTRACT_CASES'
            elif 'complete' in text and 'contract cases' in text:
                return 'COMPLETE_CONTRACT_CASES'
            else:
                return 'CONTRACT_CASE'
        elif 'loop invariant' in text:
            if 'initialization' in text or 'in first iteration' in text:
                return 'LOOP_INVARIANT_INIT'
            elif 'preservation' in text or 'after first iteration' in text:
                return 'LOOP_INVARIANT_PRESERV'
            else:
                return 'LOOP_INVARIANT'
        elif 'loop variant' in text:
            return 'LOOP_VARIANT'
        elif 'assertion' in text:
            return 'ASSERT'
        elif 'raise statement' in text or 'exception' in text:
            return 'RAISE'

        # no tag recognized
        return None

    def is_flow_tag(tag):
        """Returns True if the given tag corresponds to a flow message"""
        return tag in ("DEPENDS",
                       "GLOBAL",
                       "INITIALIZED")

    def is_proof_tag(tag):
        """Returns True if the given tag corresponds to a proof message"""
        return tag in ("DIVISION_CHECK",
                       "INDEX_CHECK",
                       "OVERFLOW_CHECK",
                       "RANGE_CHECK",
                       "LENGTH_CHECK",
                       "DISCRIMINANT_CHECK",
                       "INITIAL_CONDITION",
                       "DEFAULT_INITIAL_CONDITION",
                       "PRECONDITION",
                       "PRECONDITION_MAIN",
                       "POSTCONDITION",
                       "REFINED_POST",
                       "CONTRACT_CASE",
                       "DISJOINT_CONTRACT_CASE",
                       "COMPLETE_CONTRACT_CASE",
                       "LOOP_INVARIANT_INIT",
                       "LOOP_INVARIANT_PRESERV",
                       "LOOP_INVARIANT",
                       "LOOP_VARIANT",
                       "ASSERT",
                       "RAISE")

    def is_negative_result(result):
        """Returns True if the given result corresponds to a negative one"""
        return result != "PASS"

    def is_valid_result(result):
        """Returns True if the given result corresponds to a valid one"""
        return result in ("PASS",
                          "FAIL",
                          "CHECK",
                          "WARN",
                          "ERROR")

    def get_result(qualifier, text, is_flow_tag):
        """Returns the result for a given message qualifier and text.

        PARAMETERS
          qualifier:   either 'info' or 'warning'
          text:        text of the message, stripped of the initial qualifier
          is_flow_tag: True for flow messages, False for proof messages
        """
        if qualifier == 'info':
            if 'proved' in text or 'nonreturning' in text:
                return 'PASS'
            else:
                return None
        elif qualifier == 'warning':
            if is_flow_tag:
                return 'WARN'
            else:
                return 'FAIL'
        elif qualifier == 'low' or\
                qualifier == 'medium' or\
                qualifier == 'high':
            if is_flow_tag:
                return 'CHECK'
            else:
                return 'FAIL'
        else:
            return 'ERROR'

    def not_found(f, line, tag, result):
        """Print an error that the requested mark has not been found"""
        if is_negative_result(result):
            print "SOUNDNESS BUG",
        else:
            assert is_proof_tag(tag)
            print "PROOF REGRESSION",
        print "at " + f + ":" + str(line) + \
            ": mark @" + tag + ":" + result + " not found"

    # store actual results in a map from (file,line) to (TAG,RESULT)
    results = {}

    for msg in strlist:
        m = re.match(is_msg, msg)
        if m:
            f = m.group(1)
            line = int(m.group(2))
            qual = m.group(3)
            text = m.group(5)
            tag = get_tag(text)
            if tag:
                res = get_result(qual, text, is_flow_tag(tag))
                results.setdefault((f, line), set()).add((tag, res))

    # check that marks in source code have a matching actual result
    for f in files:
        with open(f, 'r') as ff:
            for line, linestr in enumerate(ff):
                line = line + 1  # first line in file is 1, not 0
                for mark in re.finditer(is_mark, linestr):
                    tag = mark.group(1).upper()
                    if not (is_flow_tag(tag) or is_proof_tag(tag)):
                        print "unrecognized tag", \
                            tag, "at", f + ":" + str(line)
                        sys.exit(1)
                    res = mark.group(2).upper()
                    if not is_valid_result(res):
                        print "unrecognized result", \
                            res, "at", f + ":" + str(line)
                        sys.exit(1)
                    if (f, line) not in results or \
                       (tag, res) not in results[f, line]:
                        not_found(f, line, tag, res)


def gcc(src, opt=["-c"]):
    """gcc wrapper for the testsuite

    PARAMETERS
       src: source file to process
       opt: additional options to pass to gcc
    """
    cmd = ["gcc"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    print_sorted(str.splitlines(process.out))


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

    # Otherwise, print the command output sorted
    else:
        print_sorted(str.splitlines(process.out))


def altergo(src, timeout=10, opt=None):
    """Invoke alt-ergo with why3-cpulimit wrapper

    PARAMETERS
      src: VC file to process
      timeout: timeout passed to why3-cpulimit
      opt: additional command line options for alt-ergo
    """
    cmd = ["alt-ergo", "-steps", "10000"]
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

    # generate an empty project file if not present already
    if not os.path.isfile("test.gpr"):
        with open("test.gpr", 'w') as f_prj:
            f_prj.write('project Test is\n')
            f_prj.write('  package Compiler is\n')
            f_prj.write('    for Default_Switches ("Ada") use ("-gnatws");\n')
            f_prj.write('    for Local_Configuration_Pragmas '
                        + 'use "test.adc";\n')
            f_prj.write('  end Compiler;\n')
            f_prj.write('end Test;\n')
        with open("test.adc", 'w') as f_adc:
            f_adc.write('pragma SPARK_Mode (On);\n')

    cmd = ["gnatprove"]
    # Continue on errors, to get the maximum number of messages for tests
    cmd += ["-k"]
    if quick_mode():
        cmd += ["--proof=no_wp"]
    if debug_mode():
        cmd += ["--debug"]
    if verbose_mode():
        cmd += ["--verbose"]
    cmd += to_list(opt)
    if verbose_mode():
        print cmd
    process = Run(cmd)
    # Replace line above by the one below for testing the scripts without
    # running the tool:
    # process = open("test.out", 'r').read()

    # In quick mode, ignore xfail tests by simply generating a dummy output
    if quick_mode() and xfail_test():
        if not fake_output_generated:
            fake_output_generated = True
            print "dummy output for XFAIL test"

    # Otherwise, in quick mode, ignore test output and copy instead the
    # expected output.
    elif quick_mode():
        if os.path.exists("test.out") and not fake_output_generated:
            fake_output_generated = True
            cat("test.out", True)

    # Otherwise, check marks in source code and print the command output sorted
    else:
        strlist = str.splitlines(process.out)
        # Replace line above by the one below for testing the scripts without
        # running the tool
        # strlist = str.splitlines(process)
        check_marks(strlist)
        print_sorted(strlist)


def gnatprove(opt=["-P", "test.gpr"]):
    """Invoke gnatprove

    PARAMETERS
    opt: options to give to gnatprove
    """
    gnatprove_(opt)


def prove(opt=None, steps=max_steps, procs=parallel_procs,
          vc_timeout=vc_timeout(), mode="prove"):
    """Call gnatprove with standard options"""
    fullopt = ["--report=all", "--warnings=continue"]
    fullopt += ["-P", "test.gpr", "--quiet"]
    fullopt += ["--timeout=%d" % (vc_timeout)]
    fullopt += ["--steps=%d" % (steps)]
    fullopt += ["--mode=%s" % (mode)]
    fullopt += ["-j%d" % (procs)]
    # Add opt last, so that it may include switch -cargs
    if opt is not None:
        fullopt += opt
    gnatprove(fullopt)


def do_flow(opt=None, procs=parallel_procs):
    """Call gnatprove with standard options for flow"""
    if opt is None:
        opt = []
    opt += ["--debug"]
    prove(opt, mode="flow")


def prove_all(opt=None, steps=max_steps, procs=parallel_procs,
              vc_timeout=vc_timeout()):
    """Call gnatprove with standard options to prove all VCs"""
    prove(opt, steps, procs, vc_timeout, mode="all")


def clean():
    """Call gnatprove with standard options to clean proof artifacts"""
    prove(opt=["--clean"])


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
    invert: if false, select strings that do *not* match
    """
    p = re.compile(regex)
    return [line for line in strlist if matches(p, line, invert)]


def check_all_spark(result_file, expected_len):
    """Using a gnatprove result file, check that all subprograms of that unit
       are in SPARK. Also check that there are as many entries as expected.

    PARAMETERS
        result_file      the file to read
        expected_len     the number of subprograms expected
    RESULT
        none
    """
    with open(result_file, 'r') as f:
        result = json.load(f)
        spark_result = result["spark"]
        assert len(spark_result) == expected_len
        for entry in spark_result:
            assert entry["spark"] == "all"


def check_dot_files(opt=None):
    """Call do_flow"""
    do_flow()

    # Create a list that contains all dot files lying under directory
    # gnatprove.
    dot_files = glob.glob('gnatprove/*.dot')

    # Dump the contents of all dot files on stdout
    for dot_file in sorted(dot_files):
        cat(dot_file)
