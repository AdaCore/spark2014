#!/usr/bin/env python
"""Run the testsuite for echo

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
from glob import glob
import os


def main():
    """Run the testsuite"""

    m = Main()
    add_mainloop_options(m, extended_options=True)
    add_run_test_options(m)
    m.add_option("--diffs", dest="view_diffs", action="store_true",
                 default=False, help="show diffs on stdout")
    m.parse_args()

    # Various files needed or created by the testsuite
    # creates :
    #   the ouput directory (out by default)
    #   the report file
    #   the results file

    setup_result_dir(m.options)

    if m.args:
        test_list = [t.strip('/') for t in m.args]
    else:
        test_list = sorted(glob('tests/*'))

    env = Env()

    # add support module path
    python_lib = os.path.join(os.getcwd(), 'lib', 'python')
    Env().add_search_path("PYTHONPATH", python_lib)

    env.add_search_path('PYTHONPATH', os.getcwd())
    discs = [env.target.platform]

    if m.options.discs:
        discs += m.options.discs.split(',')

    collect_result = generate_collect_result(
        m.options.output_dir, m.options.results_file, m.options.view_diffs)

    run_testcase = generate_run_testcase(python_lib + '/run-test', discs, m.options)

    MainLoop(test_list, run_testcase, collect_result, m.options.mainloop_jobs)
    # Generate the report file
    ReportDiff(m.options.output_dir,
               m.options.old_output_dir).txt_image(m.options.report_file)


if __name__ == "__main__":
    if os.path.dirname(__file__):
        os.chdir(os.path.dirname(__file__))
    main()

