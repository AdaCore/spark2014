"""
This module contains support functions for all test.py
"""

import glob
import json
import os
import re
import sys
from time import sleep
from gnatpython import fileutils
from gnatpython.env import Env
from gnatpython.ex import Run
from test_util import sort_key_for_errors


max_steps = 200
default_vc_timeout = 120
parallel_procs = 1
default_project = "test.gpr"
default_provers = ["cvc4", "altergo", "z3"]
provers_output_regex = re.compile("\((Trivial|Interval|CVC4|Z3|altergo).*\)")
default_ada = 2020

#  Change directory

TEST = sys.modules['__main__']
TESTDIR = os.path.dirname(TEST.__file__)
TEST_NAME = os.path.basename(TESTDIR)
os.chdir(TESTDIR)

#  Format of message is the following:
#     file:line:column: qualifier: text extra_text
#  from which we extract:
#  - the file (group 1)
#  - the line (group 2)
#  - the qualifier (group 3)
#  - the text (group 5)
#
#  In particular, we separate out the extra_text which starts with a comma or
#  an opening parenthesis/bracket, that introduce additional information about
#  the part of a property that cannot be proved (", cannot prove bla"), that
#  give counterexample values ("(e.g. when bla)"), or that give an explanation
#  ("[possible explanation: bla]") as including these in the text of the
#  message can lead to bad identification of the message category when a
#  variable name coincides with some substrings that are searched in text.

is_msg = re.compile(r"([\w-]*\.ad.?):(\d*):\d*:" +
                    r" (info|warning|low|medium|high)?(: )?([^(,[]*)(.*)?$")
is_mark = re.compile(r"@(\w*):(\w*)")


def debug_mode():
    return "debug" in os.environ and os.environ["debug"] == "true"


def verbose_mode():
    return "verbose" in os.environ and os.environ["verbose"] == "true"


def inverse_prover():
    return "inverse_prover" in os.environ and\
        os.environ["inverse_prover"] == "true"


def z3_counterexample():
    return "z3_counterexample" in os.environ and\
        os.environ["z3_counterexample"] == "true"


def benchmark_mode():
    return "benchmarks" in os.environ and os.environ["benchmarks"] == "true"


def cache_mode():
    return "cache" in os.environ and os.environ["cache"] == "true"


def coverage_mode():
    return "coverage" in os.environ and os.environ["coverage"] == "true"


def get_default_timeout():
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


def build_prover_switch(proverlist):
    """from a list of prover names, produce the option to be passed to
       gnatprove"""
    if len(proverlist) == 0:
        return []
    else:
        return ["--prover=" + ','.join(proverlist)]


def cat(filename, sort=False, start=1, end=0):
    """Dump the content of a file on stdout

    PARAMETERS
      filename: name of the file to print on stdout
      start: first line to output, starting from line 1
      end: last line to output if not 0
    """
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            # Dump all the file
            if end == 0:
                if sort:
                    print_sorted(f.readlines())
                else:
                    print f.read()
            # Dump only the part of the file between lines start and end
            else:
                lines = []
                for i, line in enumerate(f):
                    if i+1 >= start and i+1 <= end:
                        lines.append(line)
                if sort:
                    print_sorted(lines)
                else:
                    for line in lines:
                        print line,


def ls(directory=None, filter_output=None):
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
    if filter_output is not None:
        strlist = grep(filter_output, strlist, invert=True)
    print_sorted(strlist)


def matches(comp_reg, s, invert):
    """decide whether string s matches the compiled regex comp_reg

    PARAMETERS
    comp_reg: a compiled regex
    s: a string to be matched
    invert: if false, negate the result
    """
    m = re.match(comp_reg, s)
    return (invert and not m) or (not invert and m)


def check_counterexamples():
    """Checks that marks in source code have a matching counterexample.

    Marks are strings in the source that have the format
        @COUNTEREXAMPLE
    For each such mark, either issue an error if there is no corresponding
    counterexample, or display the counterexample trace in a human readable
    form in the output.

    """
    files = glob.glob("*.ad?")
    result_files = glob.glob("gnatprove/*.spark")
    is_mark = re.compile(r"@COUNTEREXAMPLE")

    def not_found(f, line):
        """Print an error that the requested mark has not been found"""
        print "MISSING COUNTEREXAMPLE at " + f + ":" + str(line)

    # store actual results in a map from (file,line) to a list of strings
    # for the counterexample, where each element of the list gives the
    # pairs (name,value) for the counterexample in a different line of
    # code.
    results = {}

    for result_file in result_files:
        with open(result_file, 'r') as f:
            result = json.load(f)
            proof_result = result["proof"]
            for msg in proof_result:
                msg_file = msg["file"]
                msg_line = msg["line"]

                # list of strings for the trace attached to the counterexample.
                # In fact we store here pairs of a location (file,line) and
                # a string for the trace element, so that we can sort the trace
                # based on location before displaying it.
                msg_list = []

                def str_elem(val):
                    return val["name"] + " = " + val["value"]

                def location((loc, ctx)):
                    return loc

                def trace((loc, ctx)):
                    return ctx

                if "cntexmp" in msg:
                    for ff, file_value in msg["cntexmp"].items():
                        if "current" in file_value:
                            for line, values in file_value["current"].items():
                                ctx = "  trace at " + ff + ":" + line + \
                                      " --> " + \
                                      " and ".join(map(str_elem, values))
                                msg_list.append(((ff, int(line)), ctx))
                        if "previous" in file_value:
                            for line, values in file_value["previous"].items():
                                ctx = "[PREVIOUS]  trace at " + ff + ":" + \
                                      line + " --> " + \
                                      " and ".join(map(str_elem, values))
                                msg_list.append(((ff, int(line)), ctx))

                    # sort the trace elements based on location
                    msg_list.sort(key=location)

                    # store only the list of trace elements, not locations.
                    # Note that only the last counterexample for a given
                    # location (msg_file,msg_line) is stored in results, when
                    # multiple counterexamples are present on the same line.
                    results[(msg_file, msg_line)] = map(trace, msg_list)

    # check that marks in source code have a matching counterexample, and
    # dislay the counterexample when found.
    for f in files:
        with open(f, 'r') as ff:
            for line, linestr in enumerate(ff):
                line = line + 1  # first line in file is 1, not 0
                for mark in re.finditer(is_mark, linestr):
                    if (f, line) in results:
                        print "counterexample expected for check at " + \
                            f + ":" + str(line)
                        for ctx in results[(f, line)]:
                            print ctx
                    else:
                        not_found(f, line)


def check_fail(strlist, no_failures_allowed):
    """ Makes sure that we did not have any failed proof attempts. """

    failures = frozenset(["low", "medium", "high"])

    if no_failures_allowed:
        for m in map(is_msg.match, strlist):
            if m is not None:
                kind = m.group(3)
                if kind in failures:
                    print "FAILED CHECK UNEXPECTED at %s:%s" % (m.group(1),
                                                                m.group(2))


def is_dependency_tag(tag):
    """Returns True if the given tag corresponds to a dependency flow
    message"""
    return tag in ("DEPENDS",
                   "GLOBAL")


def is_flow_initialization_tag(tag):
    """Returns True if the given tag corresponds to an initialization flow
    message"""
    return tag in ("INITIALIZED",
                   "INITIALIZES")


def is_aliasing_tag(tag):
    """Returns True if the given tag corresponds to an aliasing flow message"""
    return tag in ("ALIASING")


def is_rte_tag(tag):
    """Returns True if the given tag corresponds to a RTE proof message"""
    return tag in ("DIVISION_CHECK",
                   "INDEX_CHECK",
                   "OVERFLOW_CHECK",
                   "RANGE_CHECK",
                   "LENGTH_CHECK",
                   "DISCRIMINANT_CHECK",
                   "TAG_CHECK",
                   "NULL_EXCLUSION",
                   "MEMORY_LEAK",
                   "DEREFERENCE_CHECK")


def is_proof_initialization_tag(tag):
    """Returns True if the given tag corresponds to an initialization proof
    message"""
    return tag in ("INIT_BY_PROOF")


def is_ada_assertion_tag(tag):
    """Returns True if the given tag corresponds to an Ada assertion proof
    message"""
    return tag in ("PREDICATE_CHECK",
                   "INVARIANT_CHECK",
                   "PRECONDITION",
                   "PRECONDITION_MAIN",
                   "POSTCONDITION",
                   "ASSERT")


def is_spark_assertion_tag(tag):
    """Returns True if the given tag corresponds to an Ada assertion proof
    message"""
    return tag in ("DEFAULT_INITIAL_CONDITION",
                   "CONTRACT_CASE",
                   "DISJOINT_CONTRACT_CASE",
                   "COMPLETE_CONTRACT_CASE",
                   "LOOP_INVARIANT_INIT",
                   "LOOP_INVARIANT_PRESERV",
                   "LOOP_INVARIANT",
                   "LOOP_VARIANT",
                   "REFINED_POST")


def is_other_proof_tag(tag):
    """Returns True if the given tag corresponds to another proof message"""
    return tag in ("INITIAL_CONDITION",
                   "RAISE",
                   "TRIVIAL_PRE",
                   "WEAKER_PRE",
                   "STRONGER_POST",
                   "WEAKER_CLASSWIDE_PRE",
                   "STRONGER_CLASSWIDE_POST",
                   "UNCHECKED_CONVERSION",
                   "UNCHECKED_CONVERSION_SIZE",
                   )


def is_flow_tag(tag):
    """Returns True if the given tag corresponds to a flow message"""
    return (is_dependency_tag(tag) or
            is_flow_initialization_tag(tag) or
            is_aliasing_tag(tag))


def is_proof_tag(tag):
    """Returns True if the given tag corresponds to a proof message"""
    return (is_rte_tag(tag) or
            is_proof_initialization_tag(tag) or
            is_ada_assertion_tag(tag) or
            is_spark_assertion_tag(tag) or
            is_other_proof_tag(tag))


def check_marks(strlist):
    """Checks that marks in source code have a matching result.

    Given the output from flow analysis and/or proof, check that all marks
    mentioned in source files have a matching expected result, where source
    files are taken to be the *.ad? files in the current directory.

    Marks are any strings in the source that have the format
        @TAG:RESULT
    where both TAG and RESULT are alphanumeric strings without space, possibly
    with underscores. A tag denotes a line where some result is expected
    (typically this marker will be put in comments).

    TAG is either:
    - a check (RANGE_CHECK, DIVISION_CHECK, etc), or
    - a flow message (UNINIT, DEPENDS, etc).

    The complete list of tags is given by functions is_flow_tag and
    is_proof_tag.

    RESULT is either
    - PASS/FAIL for checks, or
    - ERROR/CHECK/WARN for flow messages, or
    - NONE for no such check/message.

    Case does not matter for the tag or result, although UPPERCASE is better in
    source code to easily locate the marks visually.

    """
    files = glob.glob("*.ad?")

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
        elif 'initializes' in text:
            return 'INITIALIZES'
        elif 'aliased' in text:
            return 'ALIASING'

        # proof tags

        # When adding a tag in this section, you need also to update the
        # function is_proof_tag below.
        if 'division check' in text or 'divide by zero' in text:
            return 'DIVISION_CHECK'
        elif 'index check' in text:
            return 'INDEX_CHECK'
        elif 'overflow check' in text:
            return 'OVERFLOW_CHECK'
        elif 'predicate check' in text:
            return 'PREDICATE_CHECK'
        elif 'invariant check' in text:
            return 'INVARIANT_CHECK'
        elif 'range check' in text:
            return 'RANGE_CHECK'
        elif 'length check' in text:
            return 'LENGTH_CHECK'
        elif 'discriminant check' in text:
            return 'DISCRIMINANT_CHECK'
        elif 'tag check' in text:
            return 'TAG_CHECK'
        elif 'initialization check' in text:
            return 'INIT_BY_PROOF'
        elif 'null exclusion check' in text:
            return 'NULL_EXCLUSION'
        elif 'memory leak' in text:
            return 'MEMORY_LEAK'
        elif 'dereference check' in text:
            return 'DEREFERENCE_CHECK'
        elif 'default initial condition' in text:
            return 'DEFAULT_INITIAL_CONDITION'
        elif 'initial condition' in text:
            return 'INITIAL_CONDITION'
        elif 'precondition' in text or 'nonreturning' in text:
            if 'of main program' in text:
                return 'PRECONDITION_MAIN'
            elif 'True' in text:
                return 'TRIVIAL_PRE'
            elif 'class-wide' in text and 'overridden' in text:
                return 'WEAKER_CLASSWIDE_PRE'
            elif 'class-wide' in text:
                return 'WEAKER_PRE'
            else:
                return 'PRECONDITION'
        elif 'postcondition' in text:
            if 'class-wide' in text and 'overridden' in text:
                return 'STRONGER_CLASSWIDE_POST'
            elif 'class-wide' in text:
                return 'STRONGER_POST'
            else:
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
            elif 'preservation' in text or 'by an arbitrary iteration' in text:
                return 'LOOP_INVARIANT_PRESERV'
            else:
                return 'LOOP_INVARIANT'
        elif 'loop variant' in text:
            return 'LOOP_VARIANT'
        elif 'assertion' in text:
            return 'ASSERT'
        elif 'raise statement' in text or 'exception' in text:
            return 'RAISE'
        elif 'bit representation' in text or 'unchecked conversion' in text:
            if 'size' in text:
                return 'UNCHECKED_CONVERSION_SIZE'
            else:
                return 'UNCHECKED_CONVERSION'

        # no tag recognized
        return None

    def is_negative_result(result):
        """Returns True if the given result corresponds to a negative one"""
        return result != "PASS"

    def is_valid_result(result):
        """Returns True if the given result corresponds to a valid one"""
        return result in ("PASS",
                          "FAIL",
                          "CHECK",
                          "WARN",
                          "ERROR",
                          "NONE")

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

    def bad_found(f, line, tag, result):
        """Print an error that the mark has been unexpectedly found"""
        print "SPURIOUS MESSAGE",
        print "at " + f + ":" + str(line) + \
            ": message @" + tag + ":" + result + " found"

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

                    if res == "NONE":
                        if (f, line) in results:
                            for tag2, res2 in results[f, line]:
                                if tag == tag2:
                                    bad_found(f, line, tag2, res2)
                    else:
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


def spark_install_path():
    """the location of the SPARK install"""
    exec_loc = fileutils.which("gnatprove")
    return os.path.dirname(os.path.dirname(exec_loc))


def altergo(src, timeout=10, opt=None):
    """Invoke alt-ergo with why3-cpulimit wrapper

    PARAMETERS
      src: VC file to process
      timeout: timeout passed to why3-cpulimit
      opt: additional command line options for alt-ergo
    """
    # add libexec/spark/bin to the PATH
    installdir = spark_install_path()
    bindir = os.path.join(installdir, 'libexec', 'spark', 'bin')
    Env().add_path(bindir)
    # run alt-ergo
    cmd = ["alt-ergo", "-steps-bound", "20000"]
    cmd += to_list(opt)
    cmd += [src]
    process = Run(cmd)
    print process.out


def strip_provers_output(s):
    """ Strip the extra output generated by --report=provers output from the
        argument string"""
    return provers_output_regex.sub("", s)


def strip_provers_output_from_testout():
    """Strip the extra output generated by --report=provers output from the
       test.out file"""
    if os.path.isfile('test.out'):
        with open("test.out", 'r') as f:
            content = f.read()
        content = strip_provers_output(content)
        with open("test.out", 'w') as f:
            f.write(content)


def gnatprove(opt=["-P", default_project], no_fail=False, no_output=False,
              filter_output=None, cache_allowed=True, subdue_flow=False,
              sort_output=True, exit_status=None, ada=default_ada):
    """Invoke gnatprove, and in case of success return list of output lines

    PARAMETERS
    opt: options to give to gnatprove
    filter_output: regex used to remove output from gnatprove
    no_fail: if set, then we make sure no unproved checks are in the output
    subdue_flow: if set, then we silence a bunch of flow warnings and the
                 check about unused globals (so we can set no_fail)
    exit_status: if set, expected value of the exit status from gnatprove
    """
    # generate an empty project file if not present already
    if not os.path.isfile(default_project):
        with open(default_project, 'w') as f_prj:
            f_prj.write('project Test is\n')
            f_prj.write('  package Compiler is\n')
            f_prj.write('    for Default_Switches ("Ada")' +
                        ' use ("-gnatws", "-gnat' + str(ada) + '");\n')
            f_prj.write('    for Local_Configuration_Pragmas' +
                        ' use "test.adc";\n')
            f_prj.write('  end Compiler;\n')
            f_prj.write('end Test;\n')
        with open("test.adc", 'w') as f_adc:
            f_adc.write('pragma SPARK_Mode (On);\n')
            f_adc.write('pragma Profile (Ravenscar);\n')
            f_adc.write('pragma Partition_Elaboration_Policy (Sequential);\n')
            if subdue_flow:
                for w in ("unused assignment",
                          "unused assignment to *",
                          "statement has no effect",
                          "unused initial value of *",
                          "* is not modified, could be INPUT",
                          "initialization of * has no effect"):
                    f_adc.write("pragma Warnings (Off, \"%s\");\n" % w)

    cmd = ["gnatprove"]
    # Continue on errors, to get the maximum number of messages for tests
    cmd += ["-k"]
    # Issue all information messages for tests
    cmd += ["--info"]
    if benchmark_mode():
        cmd += ["--benchmark"]
    if debug_mode():
        cmd += ["--debug"]
    if verbose_mode():
        cmd += ["--verbose"]
    if cache_allowed and cache_mode():
        cmd += ["--memcached-server=localhost:11211"]
    if coverage_mode():
        cmd += ["--coverage"]
    cmd += to_list(opt)
    if verbose_mode():
        print ' '.join(cmd)
    process = Run(cmd)
    # Replace line above by the one below for testing the scripts without
    # running the tool:
    # process = open("test.out", 'r').read()

    # Check marks in source code and print the command output sorted
    strlist = str.splitlines(process.out)
    # Replace line above by the one below for testing the scripts without
    # running the tool
    # strlist = str.splitlines(process)

    if inverse_prover():
        strlist = [strip_provers_output(s) for s in strlist]
        strip_provers_output_from_testout()
    if subdue_flow:
        strlist = [s for s in strlist
                   if "low: unused global" not in s]

    check_marks(strlist)
    check_fail(strlist, no_fail)
    # Check that the exit status is as expected
    if exit_status is not None and process.status != exit_status:
        print "Unexpected exit status of", process.status
        failure = True
    else:
        failure = False

    if filter_output is not None:
        strlist = grep(filter_output, strlist, invert=True)

    if not no_output or failure:
        if sort_output:
            print_sorted(strlist)
        else:
            for line in strlist:
                print line


def prove_all(opt=None, steps=None, procs=parallel_procs,
              vc_timeout=None, memlimit=None,
              mode="all", counterexample=True,
              prover=default_provers,
              cache_allowed=True,
              report="provers",
              project=default_project,
              level=None,
              no_fail=False,
              no_output=False,
              sort_output=True,
              filter_output=None,
              subdue_flow=False,
              codepeer=False,
              ada=default_ada,
              replay=False):
    """Call gnatprove with standard options.

       For option steps the default is max_steps set above, setting this
       option to zero disables steps option.

       no_fail, subdue_flow and filter_output are passed directly to
       gnatprove().
    """
    fullopt = ["--warnings=continue"]
    fullopt += ["--report=%s" % (report)]
    fullopt += ["--assumptions"]
    fullopt += ["-P", project, "--quiet"]
    if codepeer:
        fullopt += ["--codepeer=on"]
    if replay:
        fullopt += ["--replay"]

    if level is None:
        # If no proof level is specified, we use the default timeout and
        # step limit unless otherwise specified.
        if steps is None:
            steps = max_steps
        if vc_timeout is None:
            vc_timeout = get_default_timeout()
    else:
        fullopt += ["--level=%u" % level]

    if steps is not None:
        fullopt += ["--steps=%d" % steps]
    if memlimit is not None:
        fullopt += ["--memlimit=%d" % memlimit]
    if vc_timeout is not None:
        fullopt += ["--timeout=%d" % vc_timeout]

    fullopt += ["--mode=%s" % (mode)]
    fullopt += ["-j%d" % (procs)]
    if prover:
        if inverse_prover():
            inverse = prover[:]
            inverse.reverse()
            fullopt += build_prover_switch(inverse)
        else:
            fullopt += build_prover_switch(prover)
    if benchmark_mode():
        fullopt += ["--benchmark"]
    if not counterexample:
        fullopt += ["--no-counterexample"]
    if z3_counterexample():
        fullopt += ["--z3-counterexample"]
    # Add opt last, so that it may include switch -cargs
    if opt is not None:
        fullopt += opt
    gnatprove(fullopt,
              no_fail=no_fail,
              no_output=no_output,
              sort_output=sort_output,
              cache_allowed=cache_allowed,
              subdue_flow=subdue_flow,
              ada=ada,
              filter_output=filter_output)


def do_flow(opt=None, procs=parallel_procs, no_fail=False, mode="all",
            gg=True, sort_output=True, ada=default_ada):
    """
    Call gnatprove with standard options for flow. We do generate
    verification conditions, but we don't actually try very hard to
    prove anything.
    """

    if not gg:
        if opt is None:
            opt = []
        opt.append("--no-global-generation")

    prove_all(opt, procs=procs, steps=1, counterexample=False,
              prover=["cvc4"], no_fail=no_fail, mode=mode,
              sort_output=sort_output, ada=ada)


def do_flow_only(opt=None, procs=parallel_procs, no_fail=False,
                 ada=default_ada):
    """
    Similar to do_flow, but we disable VCG. Should only be used for flow
    tests that take an undue amount of time.
    """

    do_flow(opt, procs, no_fail, mode="flow", ada=ada)


def no_crash():
    """
    Only attempt to detect crashes and other unexpected behavior. No expected
    tool output is filed for such tests.
    """
    gnatprove(no_output=True, exit_status=0)


def clean():
    """Call gnatprove with standard options to clean proof artifacts"""
    prove_all(opt=["--clean"], no_fail=True)


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


def touch(fname, times=None):
    """touch a file so that it appears altered

    PARAMETERS
    fname: a string corresponding to a filename
    times: optional paramter so set the access time
    """
    with open(fname, 'a'):
        os.utime(fname, times)


def sleep_on_windows(secs=3):
    """If on Windows then sleep to stabilise the filesystem status

    PARAMETERS
    secs: number of seconds to sleep if in Windows
    """
    platform = sys.platform
    if platform.startswith('win') or platform.startswith('cygwin'):
        sleep(secs)


def check_all_spark(result_file, expected_len):
    """Using a gnatprove result file, check that all subprograms, entries, task
       bodies and packages of that unit are in SPARK. Also check that there are
       as many entries as expected.

    PARAMETERS
        result_file      the file to read
        expected_len     the number of entities expected
    RESULT
        none

    """
    with open(result_file, 'r') as f:
        result = json.load(f)
        spark_result = result["spark"]
        assert len(spark_result) == expected_len
        for entry in spark_result:
            assert entry["spark"] == "all"


def check_spec_spark(result_file, expected_len):
    """Using a gnatprove result file, check that all specs of that unit
       are in SPARK. Also check that there are as many entries as expected.

    PARAMETERS
        result_file      the file to read
        expected_len     the number of entities expected
    RESULT
        none
    """
    with open(result_file, 'r') as f:
        result = json.load(f)
        spark_result = result["spark"]
        assert len(spark_result) == expected_len
        for entry in spark_result:
            assert entry["spark"] == "spec"


def check_trace_files(only_flow=False):
    # Note that in order for check_trace_files to work, we have to call one of
    # the other functions first. Otherwise, no trace files will have been
    # generated.

    # Create a list that contains all trace files lying under directory
    # gnatprove.
    if only_flow:
        trace_files = glob.glob('gnatprove/*__flow__*.trace')
        # ??? The above pattern might also match non-flow traces created for a
        # unit with "flow" in its name, but the glob routine accepts only
        # simple patterns and not arbitrary regular expressions, so we can't do
        # better; however, this pacricular name is unlikely to happen in our
        # testsuite.
    else:
        trace_files = glob.glob('gnatprove/*.trace')

    print "Trace files' contents:"
    # Dump the contents of all trace files on stdout
    for trace_file in sorted(trace_files):
        cat(trace_file)


def check_output_file(sort=False):
    """ Print content of output file gnatprove.out.

    The goal is to make this output independent from the order of provers
    used. In particular, the summary table may contain different percentages
    for the provers used to prove the VCs, and the columns of the table may
    be aligned differently due to that.

    To avoid such differences:
    - replace all sequences of spaces by a single space
    - replace all sequences of '-' characters by a single one
    - filter out substrings starting with '(CVC4', '(altergo' or '(Z3', up
      to the following closing parenthesis.

    This ensures a common output whatever the order of provers used.
    """

    filename = os.path.join('gnatprove', 'gnatprove.out')
    prover_tag = re.compile(r"(^.*)(\((CVC4|altergo|Z3)[^\)]*\))(.*$\n)")
    output = ""

    with open(filename, 'r') as f:
        for line in f:
            m = re.match(prover_tag, line)
            if m:
                newline = m.group(1) + ' ' + m.group(4)
            else:
                newline = line
            # Replace multiple white spaces by a single one, and multiple
            # '-' characters (used for the frame of the summary tablen, whose
            # size varies depending on prover order) by a single one.
            output += re.sub(' +', ' ', re.sub('-+', '-', newline))
    if sort:
        print_sorted(str.splitlines(output))
    else:
        print output
