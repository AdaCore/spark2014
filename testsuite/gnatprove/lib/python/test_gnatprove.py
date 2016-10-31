"""Run the gnatprove testsuite

This module assumes that lib/python has been added to PYTHONPATH.
"""

from gnatpython.env import Env
from gnatpython.main import Main
from gnatpython.mainloop import (MainLoop, add_mainloop_options,
                                 generate_collect_result,
                                 generate_run_testcase,
                                 setup_result_dir)
from gnatpython.testdriver import add_run_test_options
from gnatpython.reports import ReportDiff

from collections import deque
import fnmatch
from glob import glob

import re
import os


def run_testsuite(test_driver):
    """Run the testsuite

    PARAMETERS
      test_driver: path to the test driver (e.g. lib/python/run-test)
    """
    options = __parse_options()
    env = Env()

    if options.vc_timeout:
        os.environ["vc_timeout"] = str(options.vc_timeout)
    if options.debug:
        os.environ["debug"] = "true"
    if options.verbose:
        os.environ["verbose"] = "true"
    if options.inverse_prover:
        os.environ["inverse_prover"] = "true"
    if options.benchmarks:
        os.environ["benchmarks"] = "true"
    if options.cache:
        os.environ["cache"] = "true"

    if options.test_list:
        with open(options.test_list, 'r') as f:
            test_list = f.readlines()
            test_list =\
                map(lambda s: os.path.join("tests", s.strip()), test_list)
            test_list = [t for t in test_list if os.path.isdir(t)]
    elif options.exact_name:
        test_name = os.path.join('tests/', options.run_test)
        if os.path.isdir(test_name):
            test_list = [test_name]
        else:
            print 'error: test \'' + options.run_test + '\' not found'
            exit(1)
    elif options.pattern:
        test_list = filter_list('tests/*')
        reg = re.compile(options.pattern)
        test_list = [test for test in test_list
                     if test_contains_pattern(test, reg)]
    else:
        test_list = [t for t in filter_list('tests/*', options.run_test)
                     if os.path.isdir(t)]

    # Various files needed or created by the testsuite
    setup_result_dir(options)

    discs = env.discriminants

    if options.discs:
        discs += options.discs

    run_testcase = generate_run_testcase(test_driver, discs, options)
    collect_result = generate_collect_result(
        options.output_dir, options.results_file, options.view_diffs)

    MainLoop(test_list, run_testcase, collect_result, options.mainloop_jobs)

    # Write report
    with open(options.output_dir + '/discs', 'w') as discs_f:
        discs_f.write(" ".join(discs))
    ReportDiff(options.output_dir,
               options.old_output_dir).txt_image(options.report_file)


def filter_list(pattern, run_test=""):
    """Compute the list of test matching pattern

    If run_test is not null, run only tests containing run_test
    """
    test_list = glob(pattern)
    if not run_test:
        return test_list
    else:
        return [test for test in test_list if run_test in test]


def file_contains_regex(pattern, fn):
    with open(fn, 'r') as f:
        for line in f:
            if pattern.search(line):
                return True
    return False


def test_contains_pattern(test, reg):
    files = ada_files_of_test(test)
    for fn in files:
        if file_contains_regex(reg, fn):
            return True
    return False


def ada_files_of_test(test):
    result = []
    q = deque()
    q.append(test)
    while len(q) > 0:
        dir = q.pop()
        for fn in os.listdir(dir):
            my_fn = os.path.join(dir, fn)
            if os.path.isdir(my_fn):
                q.append(my_fn)
            else:
                if fnmatch.fnmatch(my_fn, '*.ad[bs]'):
                    result.append(my_fn)
    return result


def __parse_options():
    """Parse command lines options"""
    m = Main(add_targets_options=True)
    add_mainloop_options(m, extended_options=True)
    add_run_test_options(m)
    m.add_option("--benchmarks", dest="benchmarks", action="store_true",
                 default=False, help="collect benchmarks")
    m.add_option("--debug", dest="debug", action="store_true",
                 default=False, help="output debugging information")
    m.add_option("--diffs", dest="view_diffs", action="store_true",
                 default=False, help="show diffs on stdout")
    m.add_option("--exact", dest="exact_name", action="store_true",
                 default=False, help="provide exact name of test (not regexp)")
    m.add_option("--testlist", dest="test_list", action="store",
                 type="string",
                 help="provide text file with one test per line to be run")
    m.add_option("--pattern", dest="pattern", action="store",
                 type="string",
                 help="only run tests whose ada files contain this pattern")
    m.add_option("--inverse-prover", dest="inverse_prover",
                 action="store_true",
                 default=False, help="inverse order of default provers")
    m.add_option("--vc-timeout", dest="vc_timeout", action="store",
                 type="int", help="set timeout for prover")
    m.add_option("--cache", dest="cache", action="store_true",
                 default=False, help="use memcached to speed up testsuite")
    m.parse_args()

    if m.args:
        m.options.run_test = m.args[0]
        print "Running only test '%s'" % m.options.run_test
    else:
        m.options.run_test = ""

    if m.options.discs:
        m.options.discs = m.options.discs.split(',')

    return m.options
