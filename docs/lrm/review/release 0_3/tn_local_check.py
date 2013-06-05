#!/usr/bin/env python

""" This does mostly the same as the review token commit hook,
    but is designed to run locally.

    It will echo to standard out a fixed up version of the
    review token given to it; this can be used to quickly
    apply any format changes to a token (such as new fields).

    It will then echo to standard error a list of problems
    found (some of which will have been corrected in the
    echoed output).

    The basic idea is thus:
       $ tn_local_check.py <token>.tn > foo
    Check if you're happy with it all and then:
       $ mv foo <token>.tn
"""

import sys
import os

from tn_lib import parse_tn, write_tn

# Deal with a bad command line
if len(sys.argv) != 2:
   print >> sys.stderr, "You will need to specify a file to parse."
   sys.exit(1)

# Parse TN
tmp = parse_tn(os.path.basename(sys.argv[1]), open(sys.argv[1]).read())

# Print out corrected TN
print write_tn(tmp).rstrip()

# Report on any errors
if len(tmp["errors"]):
   print >> sys.stderr, "-" * 80
   print >> sys.stderr, "The review token %s contains "\
       "the following errors:" % tmp["ticket"]
   for e in tmp["errors"]:
      print >> sys.stderr, "   - %s" % e

