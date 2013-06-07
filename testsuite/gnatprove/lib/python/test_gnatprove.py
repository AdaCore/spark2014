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
from gnatpython.testdriver import (TestRunner, IS_STATUS_FAILURE)
from gnatpython.reports import ReportDiff
from gnatpython.fileutils import (split_file, diff)
import re
import logging
import json

from glob import glob

import os

def run_testsuite(test_driver):
    """Run the testsuite

    PARAMETERS
      test_driver: path to the test driver (e.g. lib/python/run-test)
    """
    options = __parse_options()
    env = Env()

    if options.quick_run:
      os.environ["quick"] = "true"
    if options.vc_timeout:
      os.environ["vc_timeout"] = str(options.vc_timeout)
    if options.debug:
      os.environ["debug"] = "true"
    if options.verbose:
      os.environ["verbose"] = "true"

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
    ReportDiff(options.output_dir, options.old_output_dir).txt_image(options.report_file)

def filter_list(pattern, run_test=""):
    """Compute the list of test matching pattern

    If run_test is not null, run only tests containing run_test
    """
    test_list = glob(pattern)
    if not run_test:
        return test_list
    else:
        return [test for test in test_list if run_test in test]

def __parse_options():
    """Parse command lines options"""
    m = Main(add_targets_options=False)
    add_mainloop_options(m,extended_options=True)
    add_run_test_options(m)
    m.add_option("--diffs", dest="view_diffs", action="store_true",
                 default=False, help="show diffs on stdout")
    m.add_option("--quick", dest="quick_run", action="store_true",
                 default=False, help="perform a quick run (no proofs)")
    m.add_option("--debug", dest="debug", action="store_true",
                 default=False, help="output debugging information")
    m.add_option("--vc-timeout", dest="vc_timeout", action="store",
                 type="int", help="set timeout for prover")
    m.parse_args()

    if m.args:
        m.options.run_test = m.args[0]
        print "Running only test '%s'" % m.options.run_test
    else:
        m.options.run_test = ""

    if m.options.discs:
        m.options.discs = m.options.discs.split(',')

    return m.options
