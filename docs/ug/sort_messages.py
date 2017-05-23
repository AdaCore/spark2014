"""
This module implement a sorting of messages issued by GNATprove, suitable for
inclusion in the User's Guide.

It should be called with the absolute path for the command.
"""

import os
import sys

# Add directory for finding test_support
sys.path.append(os.path.normpath(os.path.join(os.path.dirname(sys.argv[0]), "../../testsuite/gnatprove/lib/python")))
from test_util import sort_key_for_errors

def print_sorted(strlist):
    strlist.sort(key=sort_key_for_errors)
    for line in strlist:
        print line, # do not add newline here, as already presentin lines read from input

if __name__ == '__main__':
    print_sorted (sys.stdin.readlines())
