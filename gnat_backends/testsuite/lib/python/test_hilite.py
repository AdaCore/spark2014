"""Run the HI-LITE testsuite

This module assumes that lib/python has been added to PYTHONPATH.
"""

from gnatpython.env import Env
from gnatpython.main import Main
from gnatpython.mainloop import (MainLoop, add_mainloop_options,
                                 generate_collect_result,
                                 generate_run_testcase)
from gnatpython.testdriver import add_run_test_options
from gnatpython.testdriver import (TestRunner, IS_STATUS_FAILURE)
from gnatpython.reports import ReportDiff
from gnatpython.fileutils import (split_file, diff)
import re
import logging
import json

from glob import glob

import os

class TestGnat2Why(TestRunner):

    def apply_output_filter(self, str_list):
        return str_list

    def compare_dicts(self, expected, current):
        """Compare two result dictionaries

        PARAMETERS
            expected: the dictionary that represents the reference
            current: the dictionary that represents the current test result
        RETURNS
            the result of the comparison, one of
            DIFF
            UOK
            OK
        """
        if expected == current:
            return "OK"
        else:
            for label, expresults in expected.iteritems():
                if not current.has_key(label):
                    return "DIFF"
                for vc in expresults['valid']:
                    if not (vc in current[label]['valid']):
                        return "DIFF"
            return "UOK"


    def analyze(self):
        """Compute test status

        REMARKS
          This method should set the final value of 'result' attribute
        """
        # Retrieve the outputs and see if we match some of the CRASH or DEAD
        # patterns
        output = split_file(self.output, ignore_errors=True)
        entire_output = "\n".join(output)
        if output:
            for pattern in self.get_status_filter():
                if re.search(pattern[0], entire_output):
                    self.result.update(pattern[1])
                    break

        # If the test status has not been updated compare output with the
        # baseline
        if self.result['result'] == 'UNKNOWN':
            expected =  split_file(self.opt_results['OUT'], ignore_errors=True)
            try:
                entire_expected = "\n".join(expected)
                outdict = json.loads(entire_output)
                expdict = json.loads(entire_expected)
                result = self.compare_dicts(expdict, outdict)
                self.result['result'] = result
                if result != 'OK':
                    diff_file = open(self.diff_output, 'w')
                    diff_file.write("expected:\n")
                    diff_file.write(json.dumps(expdict, sort_keys = True,indent=4))
                    diff_file.write("\nfound:\n")
                    diff_file.write(json.dumps(outdict, sort_keys = True,indent=4))
                    diff_file.close()
            except ValueError:
                # Process output and expected output with registered filters
                expected = self.apply_output_filter(expected)
                output = self.apply_output_filter(output)

                d = diff(expected, output)
                if d:
                    logging.debug(d)
                    self.result['result'] = 'DIFF'
                    if len(expected) == 0:
                        self.result['msg'] = 'unexpected output'
                    else:
                        self.result['msg'] = 'output'
                    diff_file = open(self.diff_output, 'w')
                    diff_file.write(d)
                    diff_file.close()
                else:
                    self.result = {'result': 'OK',
                                   'msg': '',
                                   'is_failure': False}

        if self.result['result'] == 'UOK':
            self.result['is_failure'] = False
        else:
            self.result['is_failure'] = IS_STATUS_FAILURE[self.result['result']]

        # self.opt_results['XFAIL'] contains the XFAIL comment or False
        # The status should be set to XFAIL even if the comment is empty
        if self.opt_results['XFAIL'] != False:
            if self.result['result'] in ['DIFF', 'CRASH']:
                self.result.update({'result': 'XFAIL',
                                    'msg': self.opt_results['XFAIL']})
            elif self.result['result'] == 'OK':
                self.result.update({'result': 'UOK',
                                    'msg': self.opt_results['XFAIL']})


def run_testsuite(test_driver):
    """Run the testsuite

    PARAMETERS
      test_driver: path to the test driver (e.g. lib/python/run-test)
    """
    options = __parse_options()
    env = Env()

    test_list = [t for t in filter_list('tests/*', options.run_test)
                 if os.path.isdir(t)]

    # Various files needed or created by the testsuite
    result_dir = options.output_dir
    results_file = result_dir + '/results'

    discs = env.discriminants

    if options.discs:
        discs += options.discs

    run_testcase = generate_run_testcase(test_driver, discs, options)
    collect_result = generate_collect_result(
        result_dir, results_file, options.verbose)

    MainLoop(test_list, run_testcase, collect_result, options.mainloop_jobs)

    # Write report
    with open(result_dir + '/discs', 'w') as discs_f:
        discs_f.write(" ".join(discs))
    ReportDiff(result_dir).txt_image(result_dir + '/report')

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
    add_mainloop_options(m)
    add_run_test_options(m)
    m.parse_args()

    if m.args:
        m.options.run_test = m.args[0]
        print "Running only test '%s'" % m.options.run_test
    else:
        m.options.run_test = ""

    if m.options.discs:
        m.options.discs = m.options.discs.split(',')

    return m.options
