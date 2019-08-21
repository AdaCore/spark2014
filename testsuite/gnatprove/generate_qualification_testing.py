#!/usr/bin/env python

# Helper script to generate the testing data for qualification of SPARK
# Usage: ./generate_qualification_testing.py > output_file
# expects a subdirectory 'tests' with all the tests

import glob
import os
import re
import sys

# import kinds of tags from test_support
import lib.python.test_support as ts

# define sets of tests for each TOR
tor1_spark_mode = set()
tor2_extensions = set()
tor3_legality = set()
tor4_initialization = set()
tor5_rte = set()
tor6_ada_assert = set()
tor7_spark_assert = set()
tor8_flow = set()
tor9_proof = set()


def do_test(dirname, test):
    files = glob.glob(os.path.join(dirname, os.path.join(test, "*.ad?")))

    is_spark_mode_mark = re.compile(r"(\A|\W)SPARK_Mode\W", re.I)
    is_dependency_mark = re.compile(r"(\A|\W)(Global|Depends)\s*=>", re.I)

    # collect various markers in source code
    for f in files:
        with open(f, 'r') as ff:
            for line in ff:
                # collect marks of the form @TAG:RESULT
                for mark in re.finditer(ts.is_mark, line):
                    tag = mark.group(1).upper()

                    if not (ts.is_flow_tag(tag) or ts.is_proof_tag(tag)):
                        print "unrecognized tag", \
                            tag, "at", f + ":" + str(line)
                        sys.exit(1)

                    elif (ts.is_flow_initialization_tag(tag) or
                          ts.is_proof_initialization_tag(tag)):
                        tor4_initialization.add(test)

                    elif ts.is_rte_tag(tag):
                        tor5_rte.add(test)

                    elif ts.is_ada_assertion_tag(tag):
                        tor6_ada_assert.add(test)

                    elif ts.is_spark_assertion_tag(tag):
                        tor7_spark_assert.add(test)

                    elif (ts.is_dependency_tag(tag) or
                          ts.is_aliasing_tag(tag)):
                        tor8_flow.add(test)

                    elif ts.is_other_proof_tag(tag):
                        tor9_proof.add(test)

                # collect use of SPARK_Mode aspect/pragma, which denotes that
                # SPARK_Mode boundary is explicitly checked
                if re.search(is_spark_mode_mark, line):
                    tor1_spark_mode.add(test)

                # collect use of Global/Depends contracts, which denotes that
                # dependencies are explicitly checked
                if re.search(is_dependency_mark, line):
                    tor8_flow.add(test)


def print_results():
    def print_set(s, prelude):
        print ''
        print '###############################'
        print '#   ' + prelude
        print '###############################'
        for t in sorted(s):
            print t
    print_set(tor1_spark_mode,     'TOR 1 - SPARK_Mode')
    print_set(tor2_extensions,     'TOR 2 - N/A')
    print_set(tor3_legality,       'TOR 3 - N/A')
    print_set(tor4_initialization, 'TOR 4 - initialization')
    print_set(tor5_rte,            'TOR 5 - RTE')
    print_set(tor6_ada_assert,     'TOR 6 - Ada assertions')
    print_set(tor7_spark_assert,   'TOR 7 - SPARK assertions')
    print_set(tor8_flow,           'TOR 8 - flow checking')
    print_set(tor9_proof,          'TOR 9 - proof checking')


def do_all_tests(dirname):
    for test in [d for d in os.listdir(dirname)
                 if os.path.isdir(os.path.join(dirname, d))]:
        do_test(dirname, test)
    print_results()


do_all_tests('tests')
